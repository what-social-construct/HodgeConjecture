# Intended target and equivalence bridge

Assessed: 2026-09-19 (SP83 coherent affine inverse-image opens; validated).
This is the current target-first sketch, not a second
manuscript or a new theorem. The detailed component status remains in
[GAP_MAP.md](GAP_MAP.md), with theorem scope in [CLAIM_LEDGER.md](CLAIM_LEDGER.md).

## 0. Operative plan: Chow to Betti first

Planning decision (2026-09-17): start from the actual Chow--Betti cycle map,
then ask:

> For which varieties \(X\), and which codimensions \(p\), does our
> geometric construction generate the rational Hodge classes?

The organizing data are
\(\operatorname{cl}_X^p:\mathrm{CH}^p(X)_{\mathbb Q}\to
H_B^{2p}(X,\mathbb Q)\), with Hodge membership specified independently.
Compare candidates by the algebraic cycles we can construct and their image
under this map. Establishing the map and its compatibility
is distinct from showing that the construction generates every Hodge class.
Galois actions, projectors and compactification are construction mechanisms
to introduce when the chosen geometry needs them.

Retain smooth projective complex varieties as the main setting. An auxiliary
cover is a construction choice, not a restriction in the target statement;
abelian-covered varieties remain an optional worked subclass. The immediate
question is which geometric properties let us construct cycles representing
the relevant Hodge classes upstairs. The universal target in section 1 is
unchanged. This section controls the work order; section 6 records construction history and detailed
dependencies, not a competing queue. Implementation checkpoints below are
**planned**, unless explicitly marked completed.

**Completed baseline:** SP63 proves surjectivity of actual raw/graded cycle
restriction and integral/rational Chow restriction. The full build,
734 declaration checks, 565 examples and 626 selected axiom reports pass.
The four new declarations use only the standard three logical axioms.
The existing target equivalence and finite split model are retained.

### B0. Boundary-section algebra and uniform trace landing

The immediate checkpoint returns to the existing ideal/defect route. Keep
the candidate analyses below as optional examples, rather than selecting
PB0 or an abelian family as the next implementation. The first bounded
algebraic statement is

\[
 T\subseteq R\subseteq F=\operatorname{Frac}(T),\qquad
 T\text{ normal Noetherian},\qquad
 0\ne a\in T,\quad aR\subseteq T
 \quad\Longrightarrow\quad R=T.
\]

Multiplication by `a` embeds `R` into the Noetherian `T`-module `T`, so
`R` is finite as a module; its algebra structure gives integrality, and
normality gives equality. Multiplicative closure of `R` is essential.
The self-contained adaptation is in
[`Boundary/Normalization/BoundedOverring.lean`](../HodgeConjecture/Boundary/Normalization/BoundedOverring.lean),
under `HodgeConjecture.NormalizationInertia`:

- `subalgebra_eq_bot_of_nonzero_mul_mem_base` proves that implication.
- `subalgebra_eq_bot_of_mem_colon` applies it to an existing submodule
  `M` with `0 != d in T`, `d M <= T`, and a nonzero scalar in
  `M.colon R.toSubmodule`: `s R <= M` gives `d s R <= T`.
- `colon_eq_bot_of_subalgebra_ne_bot` proves that this same transporter
  ideal is zero when `R` is a proper overring and `M` has that uniform
  denominator.

Lean's `R = bottom` means the base algebra inside `F`, not the zero ring.
Use the existing `Submodule.colon`; no second transporter object or
geometric input axiom is introduced. B0's generic algebra checkpoint is
proved: the full build and six focused regressions pass, and an enforced
allowlist checks that the three theorems use only `propext`,
`Classical.choice` and `Quot.sound`.

The actual boundary-section algebra is constructed in B1 below. B2 constructs
the genuine trace dual `T^vee_B`, with a uniform denominator
`d T^vee_B <= T`. The geometric step is then to prove
`s R_I <= T^vee_B` for every section, with `s != 0`;
membership for finitely many secant coefficients does not suffice.
B3 below constructs the boundary pole witness at a removed height-one
prime and the implication from uniform landing to the existing
`ConjugateBoundarySeparation` condition. Neither a trace-dual bound nor
normality alone proves that uniform landing. B4a adds the direct alternative
of constructing fixed--moving regular pairs; it does not establish landing.
These are boundary/cover obligations; they do not assert
convolution-defect vanishing or construct representatives of prescribed
Hodge classes. The Chow--Betti target and its class-generation obligation
remain unchanged.

### B1. Actual sections in the specified fraction field

Proved as A11ax / SP65: the full build, sixteen focused regressions and
standard-axiom allowlist for all twenty-one declarations pass. For a domain
`T` and a specified fraction field `F`,
[`AffineSections.lean`](../HodgeConjecture/Boundary/Normalization/AffineSections.lean)
constructs
\[
 \eta_V:\Gamma(V,\mathcal O)\hookrightarrow F,
 \qquad R_V=\operatorname{im}(\eta_V)
 \qquad(\varnothing\ne V\subseteq\operatorname{Spec}T).
\]
`affineSectionsToFractionField` composes Mathlib's actual generic germ
with the canonical fraction-field algebra equivalence; its compatibility
with the existing `T`-action on sections makes it an `AlgHom`.
`affineSectionsToFractionField_injective` proves injectivity, and
`affineSectionsEquivSubalgebra` identifies the actual section ring with
its range `affineSectionSubalgebra`. The map respects constants and
restriction. `affineSectionSubalgebra_anti` proves that a smaller
nonempty open `W <= V` has a larger section subalgebra `R_V <= R_W`
in the common field;
`affineSectionSubalgebra_top` identifies the full-open image with the
base subalgebra. No normality or Noetherianity is required, and no second
function field, global section-algebra instance or comparison premise is
introduced.

[`BoundarySections.lean`](../HodgeConjecture/Boundary/Normalization/BoundarySections.lean)
specializes this map to the existing `NormalizedCover C`,
\[
 T=\widetilde B_N,\qquad
 U_I=\operatorname{Spec}T\setminus V(J_{\mathrm{fm}}(I)),
 \qquad \eta_I:\Gamma(U_I,\mathcal O)\hookrightarrow N,
 \qquad R_I=\operatorname{im}(\eta_I).
\]
Here `J_fm(I)` is the existing `fixedMovingBoundaryIdeal C I`, not a new
ideal. `normalization_isFractionRing` proves that the existing `N` is the
fraction field of `T`. For `I != bottom`, `fixedLocusIdeal_ne_bot` derives
nonzero fixed-locus ideal from faithfulness on that fraction field, and
`fixedMovingBoundaryOpen_nonempty` proves the complement nonempty.
`boundarySectionsToNormalClosure`, its injectivity theorem,
`boundarySectionSubalgebra` and `boundarySectionsEquivSubalgebra` provide
the actual specialization. Use `R_I.toSubmodule` for the underlying
module rather than defining another section carrier. No separation,
uniform trace landing or boundary-pole hypothesis is needed for this map.

The section algebra constructed in B1 is the actual algebra used by B2's
conditional application of B0; the section embedding alone does not assert
its equality with the base.

### B2. Genuine trace dual and a uniform denominator

Proved as A11ay / SP66: the full build, fourteen focused regressions and
enforced standard-axiom checks for all eleven new declarations pass. For
`K = Frac(B)`, a finite separable extension `N/K`, and the integral closure
`T` of `B` in `N` with `Frac(T) = N`, use the existing Mathlib submodule
\[
 T^\vee_B
 =\{z\in N:\operatorname{Tr}_{N/K}(zt)\in B\text{ for every }t\in T\}
 =\operatorname{traceDual}_{B,K}(T).
\]
In Lean this is `Submodule.traceDual B K (1 : Submodule T N)`, not a
second trace-integrality module. Its membership uses the image of `B` in
`K`; it does not silently replace `B` by its normalization.
The generic results are in
[`TraceDualBound.lean`](../HodgeConjecture/Boundary/Normalization/TraceDualBound.lean):
`mem_traceDual_unit_iff`, `traceDual_unit_le_span_traceDual` and
`exists_nonzero_traceDual_unit_denominator`.

An integral `K`-basis of `N` has a trace-dual basis by separability. The
trace-integrality condition puts every element of `T^vee_B` in the finite
`T`-span of that dual basis. Clearing its finitely many denominators in
`Frac(T)` yields one element `0 != d in T` such that
\[
 dT^\vee_B\subseteq T.
\]
This bounds the entire trace dual, not only a specified coefficient family.
The argument assumes neither Noetherianity nor normality of `B`, and it
does not assume that the normalization is free as a `B`-module.

For the existing `NormalizedCover C`, take `T = tilde B_N` and use the
existing normal closure's finite extension. From `Algebra.IsSeparable K L`,
`C.normalClosure.isSeparable` supplies separability of `N/K` directly. The alias
`normalizationTraceDual C` denotes precisely this same Mathlib submodule
`T^vee_B`. The existing fraction-field comparison supplies `Frac(T) = N`;
no extra field, transporter or geometric-input package is introduced.
The specialization is
[`NormalizationTraceBound.lean`](../HodgeConjecture/Boundary/Normalization/NormalizationTraceBound.lean),
with denominator theorem `exists_nonzero_normalizationTraceDual_denominator`.

Under the additional `[IsNoetherianRing B]` hypothesis, the supplied finite
normalization model makes `T` Noetherian, and `T` is integrally closed in
`N`. B0 therefore applies to B1's actual boundary algebra:
\[
 0\ne s\in(T^\vee_B:R_I)\Longrightarrow R_I=T,
 \qquad R_I\ne T\Longrightarrow(T^\vee_B:R_I)=0.
\]
Here `(T^vee_B:R_I)` remains the existing
`Submodule.colon` of the trace dual and `R_I.toSubmodule`.
The consumers are `boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon`,
`boundarySectionSubalgebra_eq_bot_of_trace_landing` and
`normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot`;
the middle formulation quantifies the actual `BoundarySectionRing C I`.

The two displayed consequences do not assert a nonzero transporter exists.
B3 supplies the pole witness and separation comparison; B4 remains the
independent geometric uniform-landing obligation.

### B3. Actual boundary poles and the separation criterion

Proved as A11az / SP67: the full build, twelve focused regressions and
enforced standard-axiom checks for all nine new declarations pass, together
with the appended umbrella-export checks, fresh unchanged dependency audit
and 69-page single-manuscript checks. The generic results are in
[`SectionLocalization.lean`](../HodgeConjecture/Boundary/Normalization/SectionLocalization.lean)
and
[`HeightOneBoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/HeightOneBoundaryPole.lean).
`mem_affineSectionSubalgebra_of_localFractions` glues compatible local
fraction presentations into a genuine section with the prescribed image
under `eta_V`. `mem_affineSectionSubalgebra_of_ideal_pow_mul` applies this
to a rational function `z` satisfying `J^n z <= T` on a nonempty
`V` contained in `D(J)`.

For a Noetherian domain `T`, a nonzero ideal `J` and a height-one prime
`p` containing it, `exists_heightOne_boundary_denominator` constructs
\[
 0\ne f\in J,\qquad t\notin\mathfrak p,\qquad
 tJ^n\subseteq(f).
\]
In the one-dimensional local domain `T_p`, every nonzero prime is maximal,
so the localized `J` lies in the radical of `(f)`. Finite generation
supplies a power containment and then one denominator `t` outside `p`.
Consequently `z=t/f` is an actual section on `V`; if `z` were in `T`,
then `t` would lie in `p`. This proves
`affineSectionSubalgebra_ne_bot_of_heightOne`, with no normality, trace
condition or independently supplied pole. The pinned Mathlib proof uses
the dimension bound and prime-ideal radical description directly.

[`BoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/BoundaryPole.lean)
specializes to the existing `J_fm(I)`, `U_I`, `eta_I` and `R_I`.
Noetherian `B` and `C`'s supplied finite normalization model imply
Noetherianity of `T`. For each nontrivial `I`,
`boundarySectionSubalgebra_ne_bot_of_heightOne` gives
\[
 J_{\mathrm{fm}}(I)\subseteq\mathfrak p,\quad
 \operatorname{ht}(\mathfrak p)=1
 \quad\Longrightarrow\quad R_I\ne T.
\]
`conjugateBoundarySeparation_of_boundarySectionSubalgebra_eq_bot` therefore
derives separation whenever all these actual section algebras equal the
base. These two results need no perfect-field hypothesis.

At such a height-one boundary prime, with separable `L/K`,
`boundarySection_tracePoleWitness` applies B2 to obtain, for every
`s != 0`, an actual section whose image multiplied by `s` is outside
`T^vee_B`. `normalizationTraceDual_colon_eq_bot_of_heightOne`
expresses the same obstruction through the existing colon. Finally,
`conjugateBoundarySeparation_of_traceLanding` proves
\[
 \bigl(\forall I\ne 1,\ \exists s\in T\setminus\{0\},\quad
 sR_I\subseteq T^\vee_B\bigr)
 \quad\Longrightarrow\quad
 \operatorname{ConjugateBoundarySeparation}(C).
\]
The formal premise quantifies every actual `BoundarySectionRing C I`
element. No candidate ideal, replacement carrier or additional pole
hypothesis is added.

### B4. Independent geometric uniform landing

One remaining route is to establish the premise of that last implication
from identified geometric properties: for each nontrivial
`I`, construct a nonzero `s` and prove `s eta_I(z)` belongs to `T^vee_B`
for **every** actual boundary section `z`. A finite coefficient denominator
does not control the full section algebra. Naming a candidate ideal proves
neither its nonvanishing nor its containment in `(T^vee_B:R_I)`.
Any proposed geometric condition must be justified independently of the
desired separation conclusion. The pole construction proves the obstruction
when a height-one prime is removed; it does not assert landing universally.
This is a boundary/cover obligation, separate from Chow--Betti
class generation or convolution-defect vanishing.

### B4a. Fixed--moving regular pairs

A11ba / SP68 provides a proved direct sufficient condition for separation.
The full build, ten focused regressions and three enforced standard-axiom
checks pass. The preceding boundary-pole suite was freshly rerun after
the refactor: its twelve examples and nine-declaration allowlist pass.
The appended umbrella-export checks, fresh unchanged dependency audit,
independent Lean--TeX review and 70-page single-PDF checks pass. The full
historical verification inventory was not rerun. The prescribed-element refinement
`exists_heightOne_boundary_denominator_of_ne_zero` in
[`HeightOneBoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/HeightOneBoundaryPole.lean)
starts with any chosen `f != 0`, with no `f in J` premise, keeping the conclusion
`t` outside `p` and `t J^n <= (f)` for a height-one `p` containing `J`.
The previous existential theorem remains a wrapper with the same statement.

In [`RegularPairBoundary.lean`](../HodgeConjecture/Boundary/Normalization/RegularPairBoundary.lean),
`not_le_heightOne_of_regularPair` assumes a Noetherian domain `T`,
`f,g in J`, `f != 0`, and
`IsSMulRegular (T / Ideal.span {f}) g`. This is exactly injectivity of
multiplication by `g` on `T/(f)`. The denominator construction would give
`t g^n in (f)` at a containing height-one prime; injectivity of multiplication
by `g^n` forces `t in (f)`, contradicting `t` outside that prime. Thus
\[
 0\ne f\in J,\quad g\in J,\quad
 g:T/(f)\longrightarrow T/(f)\text{ injective}
 \quad\Longrightarrow\quad
 J\not\subseteq\mathfrak p\quad(\operatorname{ht}\mathfrak p=1).
\]
The criterion permits `(f,g)=T`, including a unit `f`; it is not the full
regular-sequence convention that additionally requires a nonzero final
quotient. No normality, perfect field, trace dual, or supplied section
landing is a hypothesis of this generic argument.

Specialize to the existing normalization `T=tilde B_N` and choose
\[
 0\ne f_I\in J_{\mathrm{fix}}(I),\qquad
 g_I\in J_{\mathrm{mov}}(I),\qquad
 g_I:T/(f_I)\longrightarrow T/(f_I)\text{ injective},
\]
where `J_fix(I)` and `J_mov(I)` are the existing fixed-locus and
moving-boundary summands of `J_fm(I)`, respectively. In Lean these are
`fixedLocusIdeal I` and
`movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I`.
`conjugateBoundarySeparation_of_fixedMoving_regularPairs` consumes these
explicit witnesses for every nontrivial `I`. Noetherian `B` and the
supplied finite normalization model give Noetherian `T`; perfectness and
trace data are not required. The notation `f_I,g_I` is for local witnesses,
not a new canonical pair, ideal, input package or projector.

The separated-summand condition is sufficient, not an equivalent or
necessary reformulation of the generic ideal criterion. For arbitrary
algebraic ideals it can fail when the moving summand is zero and the
proper fixed summand already has codimension at least two; no realization
of that example by an actual normalized cover is asserted. The generic
theorem also accepts both elements in `J_fm(I)` without requiring one
from each summand.

### B4b. Geometry-input audit and algebra controls

SP69 records the [geometric-pair input audit](working/0018-geometric-pair-input-audit.md)
before adding another conditional consumer. No instantiated
`NormalizedCover` was found in the active library. Its supplied fields
give normal-closure data, finite normalization models and a marked open
immersion. They do not give full visibility or a compatible regular
moving element. This distinction is substantive: in characteristic zero,
the degree-two model `x=t^2` with visible open `D(t)` has an etale visible
map but `J_fix=J_mov=J_fm=(t)`, leaving a height-one boundary. This is an
audited mathematical example, not a Lean-formalized normalization instance.

The research-only
[`RegularPairGeometryControls.lean`](RegularPairGeometryControls.lean)
tests the first-element choice in `Q[y][x]`. With `A=(x), M=(y)`,
`f=x,g=y` works. With the same ideals, `f=xy` leaves no regular `g in M`:
the nonzero class of `x` modulo `xy` is killed by every multiple of `y`.
The generic domain obstruction uses `a != 0`, a nonunit `b`, and
`g in (b)` modulo `ab`. All eight named diagnostics and their enforced
standard-axiom audits pass without warnings, as does the full library
build with only its two existing Challenge placeholder warnings. These
controls do not identify `A,M` with the fixed/moving ideals of any cover.
The unchanged historical inventory was not rerun; the unchanged
manuscript/PDF was not rebuilt for this research checkpoint.

Associated-prime avoidance is the relevant source/API analysis for a
chosen `f`: in a Noetherian ring, seek an element of the moving ideal
outside the finite union of associated primes of `T/(f)`. This criterion
does not prove that the geometric moving ideal avoids those primes, nor
that an arbitrary nonzero `f` will work. No general avoidance theorem is
newly formalized by SP69; exact sources are in the
[source ledger](SOURCE_LEDGER.md#geometric-input-audit-and-algebra-controls-sp69-2026-09-18).

At SP69 the choice between full-visible finite etale geometry and a
genuinely nonempty-boundary construction was unresolved. The user has
now selected the first branch; SP69 itself changed research records only,
not the active library, manuscript or PDF.

### B4c. Finite affine models and full-visible separation

SP70 implements the selected affine bridge. Start with actual finite
normal algebras and compatible marked fraction fields, including supplied
`NormalClosureData`. Prove that the canonical normalization map is an
equivalence, transport finiteness and etaleness, and construct the existing
`NormalizedCover` with the entire intermediate normalization visible.
This supplies an affine constructor, rather than only a consumer of
assumed normalized-cover data. The constructor is
`normalizedCoverOfFiniteNormalAffineModels` in
[`FiniteAffineCover.lean`](../HodgeConjecture/Boundary/Normalization/FiniteAffineCover.lean).
Its finite normal `A,S` hypotheses suffice without etaleness;
`normalizedCoordinateRing_etale` separately transports etaleness when
given for the affine algebra.

For a surjective visible open, every conjugate boundary is empty. Without
perfectness or separability, the existing core-free sheet action ensures a moved sheet
for each nontrivial subgroup, giving `J_mov(I)=J_fm(I)=top`. Boundary
separation follows directly, without a regular pair, Noetherian base or
uniform-landing hypothesis, through
`conjugateBoundarySeparation_of_surjective` in
[`FullVisibleBoundary.lean`](../HodgeConjecture/Boundary/Normalization/FullVisibleBoundary.lean).
The direct consumer
`conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels`
applies this to the constructed affine cover.
The full build, twenty focused regressions, enforced standard-axiom
audits of all seventeen new declarations and the fresh unchanged
dependency audit pass. The centralized inventory now records 798 checks,
565 examples and 690 reports after appending seventeen checks and
reports; its unchanged historical prefix was not rerun in full.

SP70 does not construct a global finite etale cover or Galois refinement,
prove a general etale-to-normality theorem, or supply Chow--Betti classes.
The main smooth-projective target is unchanged. Its two manuscript
propositions have the exact affine/full-visible hypotheses; the 71-page
PDF build, warning scan, visual checks and independent Lean--TeX review
pass. B4d below derives the affine data from a supplied finite morphism.

### B4d. Actual finite-morphism affine charts

SP71 starts with a finite scheme morphism `p:Y -> X` and affine open `U`
of `X`. Use its whole inverse image and actual rings
`B_U=Gamma(X,U)`, `A_U=Gamma(Y,p^-1 U)`, with the scalar map `p.app U`.
`finiteAffinePreimage_moduleFinite` proves the finite algebra, and
`finiteAffinePreimage_etale` derives etaleness from `IsEtale p`.
Neither requires integrality, nonemptiness or normality. The underlying
general smooth/etale affine-chart results are proved in
[`AffineEtaleAlgebra.lean`](../HodgeConjecture/Boundary/Normalization/AffineEtaleAlgebra.lean).

For integral `Y` and nonempty inverse image, explicit integral closedness
of the actual stalks gives normality of `A_U` through
`affineSections_isIntegrallyClosed_of_stalks` in
[`AffineNormality.lean`](../HodgeConjecture/Boundary/Normalization/AffineNormality.lean).
The existing `Y.functionField` is its fraction field, so
`finiteAffinePreimageNormalizationIso` in
[`FiniteAffineChart.lean`](../HodgeConjecture/Boundary/Normalization/FiniteAffineChart.lean)
identifies the actual open subscheme with the normalization. Its hom is
the canonical affine presentation followed by SP70's existing map, and
`finiteAffinePreimageNormalizationIso_hom_comp_toBase` proves equality
of the structural maps all the way to the original `X`. The normalization
is the integral closure over the image of the actual `B_U` scalar map;
injectivity is not assumed. It is finite and is etale whenever `p` is
etale. The full build, eighteen focused regressions and eleven enforced
standard-axiom audits pass. The SP70 suite was freshly rerun with twenty
regressions and seventeen audits, and the unchanged dependency audit
passes six endpoint contracts and two support reports. The central
inventory has 809 checks, 565 examples and 701 reports after appending
eleven checks and reports; the unchanged historical prefix was not
rerun in full.

The remaining geometric input is normality of stalks from the intended
smooth geometry, together with an actual global Galois refinement.
B4e--B4g below supply the actual finite generic extension and its marked
normal-closure field data. Deriving normal stalks from smoothness
remains a larger foundational task. Agreement over the
base on one chart is not yet a gluing theorem. No new cover package or
function field replaces the existing objects. The target and separate
Chow--Betti generation obligation are unchanged; the manuscript gives
the chart proposition with these exact hypotheses. Its 72-page PDF build,
warning scan, visual checks and independent Lean--TeX review pass.

### B4e. The actual dominant function-field map and finite extension

SP72 constructs `functionFieldMapOfDominant` in
[`Cycles/FunctionFieldMap.lean`](../HodgeConjecture/Cycles/FunctionFieldMap.lean).
For a dominant morphism `p:Y -> X` of integral schemes, the map
`kappa_p:K(X) -> K(Y)` is the actual generic-stalk map. It is injective,
commutes with the actual section germs on every nonempty base open,
respects identity and contravariant composition, and agrees with the
existing open-immersion isomorphism. The preceding nonempty-preimage
lemma uses only dominance; generic-point preservation uses irreducibility.

[`FiniteFunctionField.lean`](../HodgeConjecture/Boundary/Normalization/FiniteFunctionField.lean)
derives the scalar tower on every nonempty open from the same germ square.
For finite `p`, the actual finite whole-inverse-image section algebra
localizes to give `FiniteDimensional K(X) K(Y)` for this exact map.
`functionFieldMapOfDominant_finiteDimensional` selects a nonempty affine
chart internally. No normality, etaleness, Noetherianity or independent
field-extension hypothesis is required. The full build, eighteen focused
regressions and eleven enforced standard-axiom audits pass. The fresh
SP71 rerun passes eighteen regressions and eleven audits; the fresh
unchanged dependency audit passes six endpoint contracts and two support
reports. The central inventory has 820 checks, 565 examples and 712
reports after appending eleven checks and reports; its historical prefix
is unchanged and was not rerun in full.

The finite-dimensional theorem alone does not give separability; B4f
below supplies it from scheme formal unramifiedness. Actual
global finite etale Galois refinement, normal stalks from smoothness and
gluing remain separate. This field bridge supplies no new field carrier,
cover package or Chow--Betti class-generation conclusion. The manuscript
states the same generic map, germ square and finite-dimensionality.
Its 72-page PDF build, warning scan, visual checks and independent
core/manuscript review pass.

### B4f. Separability from actual scheme formal unramifiedness

SP73 implements the inspected localization route in
[`SeparableFunctionField.lean`](../HodgeConjecture/Boundary/Normalization/SeparableFunctionField.lean).
For a dominant affine formally unramified morphism `p:Y -> X` of integral
schemes, `functionFieldMapOfDominant_formallyUnramified_of_affine`
proves formal unramifiedness of the existing `kappa_p` algebra using a
nonempty affine chart. `functionFieldMapOfDominant_formallyUnramified`
chooses that chart internally; finiteness is not needed for either result.

For `B=B_U`, `A=A_U`, `K=K(X)` and `L=K(Y)`, the actual section algebra
`B -> A` is formally unramified. Localizing gives formal unramifiedness
of `A -> L`; composition and `of_comp` through the proved scalar tower
`B -> K -> L` give the property over `K`. If `p` is finite, SP72 supplies
finite-dimensionality and essential finite type, and
`functionFieldMapOfDominant_isSeparable` applies Mathlib's field theorem.
Finite etale morphisms supply the scheme formal-unramifiedness hypothesis
automatically. No normality, perfectness, characteristic zero or
Noetherianity is assumed. The full build, sixteen focused regressions
and three enforced standard-axiom audits pass. The fresh SP72 rerun
passes eighteen regressions and eleven audits; the fresh unchanged
dependency audit passes six endpoint contracts and two support reports.
The central inventory has 823 checks, 565 examples and 715 reports,
with three checks and reports appended; its historical prefix is
unchanged and was not rerun in full.

SP74 below constructs marked normal-closure field data from this actual
finite extension; SP75 then generalizes the downstream hypotheses.
Global finite etale Galois refinement,
normal stalks from smooth geometry, gluing and Chow--Betti generation
remain separate; no field carrier, map or cover package is replaced.
The 73-page PDF build, warning scan and visual checks pass.

### B4g. Construct the marked normal closure and its Galois structure

SP74 constructs the existing datum in
[`NormalClosureConstruction.lean`](../HodgeConjecture/Boundary/Normalization/NormalClosureConstruction.lean).
`NormalClosureData.ofAlgebraicClosure K L` needs only a finite field
extension. It uses the existing intermediate field
`N=IntermediateField.normalClosure K L (AlgebraicClosure L)` and marks
the canonical `L` inclusion. `ofAlgebraicClosure_embedding_apply` proves
that this is the original embedding when viewed in the ambient algebraic
closure. No parallel datum or carrier alias is introduced.

For any supplied `D : NormalClosureData K L N`, `D.isSeparable` derives
separability of `N/K` from `Algebra.IsSeparable K L`, and
`D.isGalois_of_isSeparable` combines that with normality. Neither requires
`PerfectField K`. In
[`FunctionFieldNormalClosure.lean`](../HodgeConjecture/Boundary/Normalization/FunctionFieldNormalClosure.lean),
`functionFieldNormalClosureData` applies the construction to the actual
finite generic-stalk extension. Its embedding formula preserves the
canonical upstairs-field marking; `functionFieldNormalClosure_isGalois`
uses SP73 under scheme formal unramifiedness. Finite etale morphisms
therefore qualify. The full build, twenty-two focused regressions and
seven enforced standard-axiom audits pass. The fresh SP73 rerun passes
sixteen regressions and three audits; the fresh unchanged dependency
audit passes six endpoint contracts and two support reports. The central
inventory has 830 checks, 565 examples and 722 reports, with seven checks
and reports appended; its historical prefix is unchanged and was not
rerun in full.

SP74 leaves the existing consumer signatures unchanged; SP75 below
connects these extension-specific Galois results and removes unnecessary
perfectness assumptions. A scheme-level Galois refinement, normal stalks from smoothness,
normalization gluing and Chow--Betti generation remain separate.

The SP74 audit distinguished extension-separability hypotheses from
possible complete removal in core-freeness. B4h records the implemented
refactor; no such signature changes belonged to SP74 itself.
The 74-page PDF build, warning scan, visual checks and independent
core/scheme/manuscript review pass.

### B4h. Consume local separability and remove unnecessary hypotheses

SP75 generalizes 26 existing signatures, without introducing library declarations
or parallel interfaces. Fourteen fixed-field, invariant-ring,
selector/tensor and trace/pole results now state
`[Algebra.IsSeparable K L]` explicitly. The trace denominator obtains
separability of `N/K` directly from the normal-closure datum.
Core-freeness needs neither separability nor perfectness; eleven
full-visible, inertia, sheet-extension and projector-extension consumers
therefore lose their perfect-field binders with no replacement.
Their other geometric hypotheses remain unchanged.

`NormalClosureData.isSeparable` and `.isGalois_of_isSeparable` move into
`NormalClosure.lean` under the same names. The existing `.isGalois`
retains `[PerfectField K]` as the sole compatibility wrapper, deriving
separability of `L/K` through its existing finite-dimensional field data
and delegating to the extension-specific theorem. No new carrier,
normal-closure package, map, projector or source axiom is introduced.
The new consumer suite passes 24 regressions and 29 enforced
standard-axiom audits; the updated trace and pole suites pass 14/11
and 12/9. Fresh SP74 and finite-affine-cover reruns pass 22/7 and
20/17. The central inventory has 859 checks, 565 examples and 751
reports after appending 29 checks and reports; its historical prefix
is unchanged and was not rerun in full. The 74-page PDF (785575 bytes)
passes its build, warning scan and visual checks, and independent
Lean--TeX review passes. The full build passes (3179 jobs; only the two
existing Challenge placeholder warnings). The fresh unchanged dependency
audit passes six endpoint contracts and two support reports.

The finite-normalization step identified at SP75 is implemented in B4i;
the preceding validation figures retain their original SP75 scope.

### B4i. Construct the finite normal-closure model and actual affine cover

SP76's `FiniteNormalClosure.lean` first proves
`normalizedCoordinateRing_finite_of_isSeparable` by applying Mathlib's
`IsIntegralClosure.finite`: a normal Noetherian domain, its fraction field,
compatible scalar towers and a finite separable extension suffice. No
dimension-one, Dedekind or perfect-field hypothesis is used.
`normalClosureNormalizationRing_finite` specializes this to the existing
marked normal closure, using `D.finiteNormal` and `D.isSeparable`.

`normalizedCoverOfFiniteNormalAffineModel` consequently needs only one
finite normal intermediate algebra `A`, not a separately supplied second
finite normal algebra `S`. Its visible map is the existing
`intermediateToNormalization`; the corresponding separation theorem
uses that map's surjectivity and the full-visible boundary result.

For an actual finite dominant formally unramified morphism `p:Y -> X`
of integral schemes and nonempty affine `U`,
`functionFieldNormalClosure_normalization_finite` proves finiteness of
the normalization in the constructed normal closure of `K(Y)/K(X)`.
It assumes `IsIntegrallyClosed Γ(X,U)` and `IsNoetherianRing Γ(X,U)`.
With explicit normal stalks on `V=p⁻¹U`,
`finiteAffinePreimageNormalizedCover` builds the existing cover with
visible scheme `V.toScheme`, map
`(finiteAffinePreimageNormalizationIso p U hU hNormal).hom`, and datum
`functionFieldNormalClosureData p`.
`conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover` then
proves separation. The scalar maps are the existing generic germs and
`kappa_p`; neither the fields nor their marking are replaced. Finite
etale morphisms supply the formal-unramifiedness premise. No new carrier,
cover package or source axiom is introduced. The full build passes
(3180 jobs; only the two existing Challenge placeholder warnings).
The new suite passes 23 examples and seven enforced standard-three
axiom audits; fresh consumer, affine-chart and normal-closure reruns
pass 24/29, 18/11 and 22/7. The central inventory has 866 checks,
565 examples and 758 reports after appending seven checks and reports;
its historical prefix is unchanged and was not rerun in full. The
74-page PDF (788608 bytes) passes its build, warning scan and visual
checks; independent code and Lean--TeX reviews pass. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.

The subsequent tensor construction in B4j--B4m addresses the specific
normal-closure normalization `T=IntCl_B(N)` from the actual finite etale
algebra `A/B`. B4m proves its integral factor and whole-ring
finite-etale structure by a trace section; the checkpoint is validated.
Finiteness and full-visible separation alone do not imply etaleness.
SP81 in B4n implements the actual affine cover and finite-etale morphisms,
with validation complete. Localization/overlap compatibility, cocycles,
gluing and the global Galois action remain separate obligations. The
SP76 interfaces retain explicit base normality/Noetherianity and upstairs
normal stalks; deriving the stalk inputs from smooth geometry and proving
Chow--Betti generation remain separate tasks.

### B4j. Construct the finite tensor source and its marked evaluations

SP77 works with the existing finite-index tensor product and existing
marked normal closure. Put `Σ=Hom_K(L,N)`,
`P_K=⊗_{Σ,K} L` and `P_B=⊗_{Σ,B} IntCl_B(L)`.
`FiniteTensorProduct.lean` proves finiteness and etaleness of finite tensor
products from the respective properties of their factors, by finite-index
induction and existing binary tensor APIs. Empty, singleton and reindexed
products are included; no new tensor carrier is introduced.

`NormalClosureTensor.lean` constructs the multiplication evaluation
`ev_K:P_K -> N`. Each tensor factor evaluates by its corresponding
embedding. The range is an intermediate field because `N/K` is algebraic;
it contains every conjugate of `L`, so the given normal-closure property
proves that it is all of `N`. Thus `m=ker(ev_K)` is maximal and
`P_K/m ≃_K N`, with the quotient comparison commuting on every
representative. Neither separability nor an independent surjectivity
hypothesis is required.

`NormalizationTensor.lean` restricts those same embeddings to the existing
integral closures and constructs `ev_B:P_B -> IntCl_B(N)`. Its factor map
is exactly `normalizationMap N (σ.restrictScalars B)`. Including the value
of an integral pure tensor into `N` gives the value of the corresponding
field pure tensor under `ev_K`. This is a proved formula for the actual
maps, not a supplied commuting-square assumption. An actual finite normal
intermediate affine algebra `A` with fraction field `L` supplies finiteness
of `P_B`; if `A/B` is etale, it also supplies etaleness of `P_B`, using the
existing normalization equivalence. The two source-property theorems omit
the four unused base/target scalar assumptions; the evaluation maps retain
their needed compatible scalar towers. All 17 new APIs compile. The
central inventory is 883 checks, 565 examples and 775 reports after
appending 17 checks and reports; its historical prefix is unchanged and
was not rerun in full. The 76-page PDF (805454 bytes) passes its build,
warning scan and visual checks; independent code and Lean--TeX review pass.
The full build passes (3187 jobs; only the two existing Challenge
placeholder warnings). The new suite passes 28 examples and 17 enforced
standard-three axiom audits without warnings. Fresh SP76 and SP74 reruns
pass 23/7 and 22/7, respectively: 73 examples and 31 audits in these three
suites. The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports.

SP78 in B4k below constructs the canonical base-change comparison and
full evaluator square left open here; the preceding validation figures
retain their SP77 scope. SP79 in B4l constructs the selected generic
factor and canonical idempotent under separability. SP80 in B4m proves
the actual integral factor and whole-ring etaleness through a trace
section; the checkpoint is validated. The integral selector, evaluation
surjectivity and quotient comparison are constructed, not additional
hypotheses. SP81 in B4n implements the actual affine cover and morphisms,
with validation complete. Localization/overlap compatibility, cocycles,
gluing and the global Galois action remain
subsequent steps. The independent Chow--Betti generation obligation is
unchanged.

### B4k. Identify the tensor base change and full evaluator square

SP78's `PiTensorBaseChange.lean` constructs finite-index tensor base change
and factorwise algebra congruence, with exact factor/pure-tensor formulas.
The underlying tensor carriers are unchanged, including the empty-index
case of the generic base-change theorem.

`NormalizationBaseChange.lean` first constructs
`β_L:K⊗_B IntCl_B(L) ≃_K L`, sending `k⊗x` to `algebraMap K L k * x`.
It uses the specified fraction field, compatible scalar towers and
algebraicity of `L/K`; it needs neither normality nor Noetherianity of
`B`, separability or finite degree. Localization of integral closure and
the actual localization pushout supply this equivalence.

For the existing marked normal closure, finite-index tensor base change
followed by the factorwise `β_L` comparison constructs
`β_Σ:K⊗_B P_B ≃_K P_K`. The full compatibility is
`ev_K∘β_Σ=β_N∘(1_K⊗ev_B)` as algebra homomorphisms, where `β_N` is
the same one-factor construction for `N`. Thus both routes use the
original integral evaluation and marked field evaluation, not separately
chosen maps. The three common evaluation helpers move unchanged into
`FiniteTensorProduct.lean`; their public names are preserved and no
parallel evaluator or source axiom is added. The central inventory is 896
checks, 565 examples and 788 reports; its historical prefix is unchanged
and was not rerun in full. The 76-page PDF (812185 bytes) passes its build,
warning scan and visual checks. Both new leaves compile without warnings.
The focused suite passes 25 examples and 13 enforced standard-three axiom
audits, including three actual function-field cases. The full build passes
(3189 jobs; only the two existing Challenge placeholder warnings).
Fresh SP77, SP76 and SP74 reruns pass 28/17, 23/7 and 22/7, respectively:
98 examples and 44 enforced axiom audits across the four suites. The fresh
unchanged dependency audit passes six primary endpoint contracts and two
support reports.

SP79 in B4l supplies the separable generic direct-factor/idempotent
construction. SP80 in B4m proves its integral comparison and the
actual finite etale normalization via a trace section. SP81 implements
the actual affine cover and morphisms, with validation complete.
Localization/overlap compatibility, cocycles, gluing, the global Galois action and
independent Chow--Betti generation remain subsequent steps.

### B4l. Select the actual generic evaluation factor

`ReducedArtinianFactor.lean` constructs a specified field-quotient factor
of a reduced Artinian algebra from the existing maximal-ideal product
decomposition. For any surjective `f:P -> N`, the equivalence
`P ≃ N × Π_{I ≠ ker(f)} P/I` has first projection exactly `f`.
Its inverse image `e` of `(1,0)` satisfies `e²=e`, `f(e)=1`,
`e*x=0 ↔ f(x)=0` and `ker(f)=(1-e)`. Value one and annihilation of
the kernel determine it uniquely, without a separate idempotence premise.

`NormalClosureFactor.lean` proves `P_K` finite without separability and
etale under `Algebra.IsSeparable K L`. Reduced Artinianness follows;
the existing surjectivity of `ev_K` then selects the actual marked field
factor. Write `Q_m=Π_{I ≠ m} P_K/I`, `Φ_m:P_K ≃_K N × Q_m`, and
`e_m=Φ_m⁻¹(1,0)`, where `m=ker(ev_K)`. The first-projection identity
`pr₁∘Φ_m=ev_K` is equality of algebra homomorphisms, not a supplied
compatibility condition. All carriers, the field marking and the
evaluation remain unchanged. The sixteen APIs comprise nine generic
and seven normal-closure declarations. Both leaves compile without
warnings; the 3195-job full build passes. The focused suite and four
fresh neighbor suites pass 123 examples and 60 enforced standard-three
axiom audits. The fresh unchanged dependency audit passes six primary
endpoint contracts and two support reports. The PDF and independent
mathematical/Lean--TeX reviews pass; detailed validation is in the
SP79 parity-queue entry.

This is an algebra-factor selector, not a new Chow projector. It does
not provide a unital `K`-algebra section `N -> P_K`: the other factors
need not admit a `K`-algebra map from `N`. Stacks Lemma 10.143.4,
Tag 00U3, is checked for the standard classification of etale
field-algebras only; the selected factor and map comparisons are direct
Lean proofs.

SP80 in B4m constructs an integral selector directly using the unramified
separability tensor and integral trace. This bypasses the proposed proof
that the whole `P_B` is integrally closed inside `P_K`; that stronger
statement is not asserted. The idempotent equation alone would not
establish membership in `P_B`. The field decomposition and this integral
construction are compared through the existing `β_Σ`, with no new
field marking or chosen factor.

### B4m. Construct the actual integral factor by the trace section

SP80 is proved and validated. Let `B` be a
normal domain, `K` its specified fraction field, `N/K` finite, and
`T=IntCl_B(N)`. For a formally unramified, essentially finite-type
`B`-algebra `S` and an actual `B`-algebra map `f:S -> T`, the existing
unramified separability tensor supplies an `S`-linear section
`T -> S⊗_B T`. Contract its second factor by the integral trace `T -> B`.
`UnramifiedIntegralFactor.lean` thereby constructs a `B`-linear map
`r:T -> S` with `r(f(s)*t)=s*r(t)`.

Assume the image of `S` in `N` spans `N` over `K`. Its separability
tensor then centralizes both field factors. The direct contraction
identity in `SeparabilityTrace.lean` shows `f(r(t))=t` for every `t∈T`.
Thus the entire integral evaluation is surjective. Setting `E=r(1)`
gives `E*s=r(f(s))`, `E²=E`, `f(E)=1`, `E*s=0 ↔ f(s)=0`, and
`ker(f)=(1-E)`. This argument uses neither Noetherianity of `B`,
normality or flatness of `S`, nor surjectivity as an input. The section
is a linear map with the displayed source-action law, not an asserted
unital algebra map.

For the marked normal closure, `normalizationTensorEvaluation_span` in
`NormalizationBaseChange.lean` derives the spanning condition from
SP78's full evaluator square and the proved surjectivity of `ev_K`.
An actual finite normal etale intermediate `B`-algebra `A`, with the
specified fraction field `L` and compatible scalar towers, supplies the
finite etale structure on the existing `P_B` from SP77. The specialization
in `NormalizationIntegralFactor.lean` gives `r_B:T -> P_B`,
`E_m=r_B(1)`, and an evaluation-preserving algebra equivalence
`P_B/(1-E_m) ≃_B T`. Finiteness descends through this actual quotient.
The same surjective evaluation and complementary-kernel formula identify
`T` with localization of `P_B` away from `E_m`; etaleness follows by
localization and composition. No second normalization model, separately
supplied integral image, or generic-to-integral normality premise is used.

Under `Algebra.IsSeparable K L`, comparison with the previously selected
generic idempotent gives `β_Σ(1⊗E_m)=e_m`. The base-change map and both
evaluators remain the existing ones. Separability is required for this
comparison with SP79, not an additional premise of the integral section
or whole-ring finite-etale conclusion.

The exact standard source checked for this route is
[Stacks, Lemma 10.151.4, Tag 02FL](https://stacks.math.columbia.edu/tag/02FL),
for the unramified diagonal localization and separability tensor only.
The trace contraction, actual section, integral factor and normalization
identification are direct project proofs. Full-source normality remains
unproved and unnecessary for this route. All 28 APIs compile without
warnings. The full build passes 3198 jobs with only the two unchanged
Challenge warnings. The focused suite and five fresh neighbor suites
pass 153 examples and 88 enforced standard-three axiom audits. The
unchanged dependency audit passes six primary contracts and two support
reports. The 79-page PDF (826296 bytes), eight-page visual review and
independent mathematical/Lean--TeX reviews pass. The central inventory
is 940 checks, 565 examples and 832 reports; its historical prefix is
unchanged and was not rerun in full. The SP80 parity-queue entry records
the complete validation.

The focused suite verifies the ring-level specialization to an actual
finite dominant etale morphism and a nonempty affine base chart. Both
section-ring normality inputs follow from normal stalks; the original
function fields, structural maps and marked normal closure give the
finite etale normalization without a Noetherianity premise. SP81 in B4n
implements the named actual affine normalized cover, its structural maps
and marked refinement as finite etale morphisms; the checkpoint is validated.
Localization/overlap compatibility, cocycles, gluing and the global
Galois action remain subsequent steps. The earlier affine-cover
interfaces retain their stronger base-normality/Noetherianity and
upstairs-normal-stalk inputs. Deriving the stalk inputs from smooth
geometry and the independent Chow--Betti generation problem remain separate.

### B4n. Construct the actual finite etale affine refinement

SP81 is proved and validated. For integral
schemes and a finite dominant etale morphism `p:Y -> X`, let `U` be a
nonempty affine open, `V=p⁻¹U`, `B_U=Γ(X,U)`, and `A_U=Γ(Y,V)`.
Normal stalks on `U` and `V` are explicit. They give normal section
rings; the original function fields, scalar maps and marked normal
closure are retained. `FiniteEtaleNormalClosure.lean` promotes SP80's
ring-level specialization to the named
`functionFieldNormalClosure_normalization_finite_etale` and constructs
`finiteEtaleAffinePreimageNormalizedCover` in the existing `NormalizedCover`
type. Its visible scheme and map are the actual `V` and the existing
`finiteAffinePreimageNormalizationIso`. No Noetherianity, second field
marking or new cover package is introduced. The normal-closure datum
equality is literal, and full visibility gives boundary separation.

The existing structural map from the normal-closure normalization to
`Spec B_U`, and its composite to the actual `U` through the canonical
affine presentation, are finite etale. The new refinement to `V` is the
original marked normalization leg followed by the inverse of that same
visible normalization isomorphism. Composing back with the isomorphism
recovers the original leg. Composing with the actual restricted `p`
gives exactly the chart structural map, and the corresponding composite
over `X` is also proved. Finiteness of this refinement comes from the
actual finite algebra map; etaleness follows from the exact factorization
between schemes etale over `U`.
The manuscript writes the same chartwise normalization as `Z_U`, its
structural map as `π_U:Z_U -> U`, and its refinement as `λ_U:Z_U -> V`;
the factorization is `p|_V∘λ_U=π_U`.
Both maps are surjective by lying over for the actual injective integral
normalization maps. The separate theorem for `π_U` needs only a dominant
map of integral schemes and the nonempty affine chart, with no finite,
etale or normal-stalk premise. The theorem for `λ_U` uses finite dominant
`p` and normal stalks on `V`, but neither etaleness nor normality on `U`.
The finite-etale endpoints retain the stated `hX` and `hY` hypotheses.

The scheme-etale conclusion uses the actual intermediate morphism's
local standard-smooth presentations. The generic helper
`piTensorProduct_ringHomProperty` preserves a ring-map property stable
under isomorphism, identity, composition and base change on the existing
finite-index tensor carrier. `piTensorProduct_isEtale` in
`EtaleTensorSource.lean` applies this to the presentations defining
scheme etaleness. SP80's surjective evaluation and complementary-idempotent
kernel identify `Spec(ev_B)` as an open immersion, so its composite with
that etale tensor source is etale. A general `Algebra.Etale`-to-`IsEtale`
converse is absent from the pinned API and is not postulated here.

All 19 APIs compile without warnings in the 2761-job scoped build:
seventeen in the main module and two tensor helpers. The 81-page PDF
(831678 bytes) has a clean final warning/reference/box scan and passes
visual review of pages 12, 13, 61, 72 and 78. Independent geometry and
Lean--TeX reviews pass. The focused suite passes 25 examples and all
19 enforced standard-three axiom audits without warnings. Five fresh
neighbor suites also pass; the six suites total 146 examples and
89 enforced audits, with no warnings or errors. The full build passes
3200 jobs with only the two unchanged Challenge warnings. The unchanged
dependency audit passes six primary contracts and two support reports.
All nineteen API parity checks pass. The static central inventory is
959 checks, 565 examples and 851 reports; its historical prefix is
unchanged and the historical file was not re-elaborated. The SP81
parity-queue entry records the complete validation. Standard
composition/base-change/open-immersion stability and the etale cancellation
law have been checked in their exact source scope; the marked cover and
factorization identities are direct project constructions.

The next bounded localization step is B4o below; overlap comparisons,
cocycle identities, gluing and compatibility of the global Galois action
follow it. The chartwise construction is not itself a gluing theorem.
Deriving the normal-stalk inputs from smooth geometry and Chow--Betti
generation remain separate.

### B4o. Localize the same normalization and restrict the actual chart

SP82 is proved and validated. Its 28 production APIs compile cleanly in
the 2764-job scoped build; the focused suite passes 39 examples and
28 enforced standard-three axiom audits without warnings or errors.
For compatible base algebras `B -> C -> E`, retain the existing
`IntCl_B(E)` and `IntCl_C(E)` as subrings of the same `E`. The canonical
map `rho^E_{B,C}` keeps each ambient element unchanged. Identity,
composition and naturality with an ambient `C`-algebra homomorphism are
proved strict map equalities. If `C` is the localization of `B` at `M`,
the comparison exhibits `IntCl_C(E)` as the localization of `IntCl_B(E)` at
the images of `M`. The `C`-action on `E` and scalar-tower law already
encode that the denominators become units in the unchanged ambient ring.
No normality, Noetherianity or finite-field-extension hypothesis is
needed for this algebraic comparison.

For principal localization, the resulting geometric identification is

\[
 \operatorname{Spec}\operatorname{IntCl}_{B_f}(E)
 \simeq \mu_E^{-1}(D(f))
 \subseteq \operatorname{Spec}\operatorname{IntCl}_{B}(E).
\]

The tensor comparison `C tensor_B IntCl_B(E) ~= IntCl_C(E)` preserves
the actual scalar map and ambient inclusion on pure tensors. Its
contravariant map `j^E=Spec(rho)` satisfies structural and naturality
squares, together with the generic identity and composition laws.
The actual adapter uses an integral scheme's existing section rings,
restriction maps and ambient-field scalar towers. It retains the same
normal closure rather than choosing another over the smaller chart.

For any nonempty affine `W <= U`, write `j^N_{W,U}:Z_W -> Z_U` for
this restriction and `iota:W -> U`, `tilde-iota:p⁻¹W -> p⁻¹U` for the
actual inclusions. The two proved equalities are
`pi_U after j = iota after pi_W` and
`lambda_U after j = tilde-iota after lambda_W`. The latter uses the
proved restriction naturality of the existing normalization isomorphism.
The structural square requires dominant `p`; the marked square adds
finiteness and normal stalks on the two inverse images. Neither square
requires etaleness, base normality or Noetherianity. Principal subcharts
also have the proved actual localization/open-immersion endpoints.

The inventory is 17 generic localization APIs, nine actual-restriction
APIs and two marked normal-closure restriction APIs. Three fresh neighbor
suites also pass; the four suites total 107 examples and 71 audits,
without warnings or errors. The full build passes 3203 jobs with only
the two unchanged Challenge warnings. The unchanged dependency audit
passes six primary contracts and two support reports. All 28 API parity
checks and independent review pass. The 81-page PDF (835379 bytes)
has a clean final log and visual review of pages 13, 14, 61, 62, 73,
74 and 81. The static central inventory is 987 checks, 565 examples
and 879 reports; its historical prefix is unchanged and was not
re-elaborated in full. The SP82 parity-queue entry records the complete
validation.

SP83 supplies the actual restriction coherence and affine inverse-image
comparisons in B4p below. Global gluing and the compatible Galois action
remain next; normal stalks from smooth geometry and Chow--Betti generation
are separate obligations.

### B4p. Coherent affine inverse-image opens

Retain the same `Z_U = Spec IntCl_{Gamma(U)}(N)` and original
`mu_U : Z_U -> X`. The actual `j^N_{W,U}` satisfy identity, composition
and common-refinement diamonds, and commute with `mu_U`. For arbitrary
nested nonempty affine opens `W <= U`, the map is an open immersion
whose range is exactly `mu_U^-1(W)`. Thus the local comparison is an
actual open-subscheme identification, not just a field isomorphism.

Common principal neighborhoods in the two charts provide injectivity,
local open immersion and both range inclusions. No separatedness or
affineness of intersections is assumed. No finiteness, normality or
Noetherianity is needed beyond integral `X`, nonempty affine charts and
the fixed field extension. Seven coherence/range adapters and three
arbitrary-affine endpoints compile cleanly in the 2740-job scoped build.
SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

Next use nonempty affine opens as the inclusion-indexed chart diagram.
Prove the locally directed condition by common principal refinement of
points, then apply scheme gluing and descend the marked maps/action.
The chain identities alone do not instantiate that gluing package; in
particular, `Spec IntCl Gamma(U intersect W)` is not identified with
the geometric overlap when the intersection is non-affine.

The concrete next interface is Mathlib's locally directed diagram
construction in `AlgebraicGeometry/Gluing.lean`: supply open immersions
for all diagram maps and `(F comp Scheme.forget).IsLocallyDirected`,
then use its `HasColimit` and `Scheme.IsLocallyDirected.openCover`.
For the pointwise condition, equal images in a common upper chart must
lift through one common smaller affine chart. SP83's exact range and
injectivity endpoints are the named consumers for that proof. This is
an implementation plan, not a claimed instance of those interfaces.

### G0. Smooth projective setting and candidate constructions

Keep the following three outcomes distinct: a formalization of a known
geometric case; a projector-extension/realization theorem; and a new
class-generation theorem. Success at the first two is not automatically
the third. Keep one manuscript; these are proof scopes, not separate papers.

Comparison and main-setting decision assessed on 2026-09-17. Work with a
smooth projective complex target `X` and a specified codimension `p`.
For the finite etale branch, take `X` connected and distinguish an auxiliary
cover `Y -> X` from the target. Galois closure supplies deck-group structure;
neither it nor abelian geometry is a prerequisite for trace descent.
Cycle-map targets below use untwisted rational Betti degree `2p`; the
corresponding class line has Tate type `Q(-p)` when packaged as a Hodge morphism.

| Candidate | Cycles and intended Betti image | Priority and first missing geometric bridge |
| --- | --- | --- |
| Smooth projective `X`, with an optional connected finite etale cover `f:Y -> X` | Explicit cycles on `X`, or cycles on `Y` representing `f^*` of the prescribed Hodge classes | Main setting. Identify geometric hypotheses and calculate the cycle-class image; smoothness, projectivity and existence of a cover alone do not prove generation. |
| Upstairs projective bundle `Y=P_S(V)` over a smooth projective base of dimension at most two | Powers of the relative hyperplane class applied to pullbacks of fundamental classes, divisors and points on `S` | Optional deferred non-abelian example. Its classical generation and closure-stability deductions are preserved below; PB0's polynomial chart is its first Lean target if resumed, not the current work order. This does not restrict the main target to such covers. |
| Projective line, `p=1` | Point divisors and their degree; a minimal positive-dimensional normalization test | Calibration only. Actual `Proj` exists; its polynomial specialization, charts, divisor calculation and genuine `H_B^2` comparison still need construction. It does not supply the elliptic-cover family. |
| A. Pointed elliptic curve `E/C`, `p=1` | Point divisors; the first comparison is `cl(D) = deg(D) cl([0])`, with `cl([0])` generating the independently computed `H_B^2(E,Q)` | Optional seed for the abelian-covered example. Build the actual proper curve and chart/point identifications, then principal-degree zero and the positive-degree Betti comparison. Do not identify `CH^1(E)_Q` itself with `Q`. |
| Powers `E^n` and abelian varieties isogenous to them, `0 <= p <= n` | Products of divisor classes, including endomorphism-graph contributions when needed; these generate the rational Hodge classes | Optional known-generation example. `E^2,p=1` tests factors and graph divisors; higher powers need actual intersection/cup compatibility and the divisor-generation theorem. |
| Smooth projective targets finite-etale-covered by that upstairs class | Degree-normalized pushforwards of products of upstairs divisors | Optional worked subclass, detailed below. Genuine finite-cover Chow pushforward and Betti trace are missing; Galois closure adds a stable deck-group presentation. |
| B. Kuga--Sato compactification and Scholl's signed projector | The cuspidal factor lies in degree `k+1` and has only types `(k+1,0)` and `(0,k+1)` for fiber power `k >= 1` | Later projector/boundary test. This factor has no nonzero rational `(p,p)` classes, so it is not the first nonzero class-generation target. This says nothing comparable about every other factor of the whole variety. |

The optional elliptic seed uses the divisor/Chern-class comparison in
[Deligne, section 2(iii)](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf).
The known upstairs coverage result is stated in
[Milne, *Shimura varieties and moduli*, proof of Theorem 9.17, Step 1,
printed p. 519](https://www.jmilne.org/math/xnotes/svhIP.pdf): Hodge classes
on powers of an elliptic curve are generated by divisor classes. Passing
to an isogenous abelian variety uses the rational cohomology isomorphism
and compatibility with divisor pullback. This is not a result for arbitrary
abelian varieties or all products of arbitrary curves.

For B, [Scholl, Theorem 1.2.1 and section 1.2.2](https://www.dpmms.cam.ac.uk/~ajs1005/preprints/mf.pdf)
identifies the selected Chow factor with parabolic cohomology.
[Zucker, section 12, Proposition 12.5 and Lemmas 12.14--12.15](https://www.math.stonybrook.edu/~cschnell/mat690/Zucker.pdf)
gives its Hodge types. The absence of a diagonal component is the deduction
used in the table; a Tate twist shifts both indices equally and does not
change this conclusion. Products or other factors require a new target
comparison. Scholl's individual-newform decomposition in Theorem 1.2.4
uses homological motives, not a proved decomposition modulo rational equivalence.

Higher-dimensional Abelian-type Kuga families (candidate C) remain
deferred. [Wildeshaus, Theorems 0.1(d) and 0.2](https://arxiv.org/pdf/1211.5327)
extends an existing Chow idempotent and compares intermediate-extension
realizations in its specified setting; it does not supply arbitrary
Hodge-class generation.

#### General smooth projective cover construction

Given a connected finite etale surjection `f:Y -> X`, with `X` smooth
projective connected over `C`, choose a connected finite etale Galois cover
`g:Z -> X` dominating it, using
[Stacks, Tag 03SF](https://stacks.math.columbia.edu/tag/03SF).
Both `Y` and `Z` are smooth projective: etaleness preserves smoothness over
`C`, and finite covers are proper with ample pullback from `X`
([Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)).
This deduction needs no abelian hypothesis. Preservation of any stronger
property used to generate cycles is a separate question.

Do not presume that every `X` has a useful nontrivial finite etale cover.
For a target with trivial etale fundamental group, the connected cover
branch offers only the identity cover. A direct cycle construction remains
available as a route; merely taking `Y=X` provides no generation argument.

#### Optional worked subclass: elliptic-power-covered targets

For this example only, fix a complex elliptic curve `E`. Consider smooth
projective connected `X` admitting a finite etale surjection `f:A -> X`, where `A` is an abelian
variety isogenous to `E^n`, `n >= 1`. This is a geometric membership
condition, not the definition of the main target class or an assumption
that the desired Hodge classes are algebraic.
All statements in this paragraph concern classical geometry; their Lean
instances are not yet constructed.

By [Stacks, Tag 03SF](https://stacks.math.columbia.edu/tag/03SF), a connected
finite etale Galois cover `g:Z -> X` can dominate `A -> X`. The induced
`Z -> A` is finite etale. Choosing a point over the origin makes it an
isogeny of abelian varieties, by
[Milne, *Abelian Varieties*, Remark 15.3, printed p. 28](https://www.jmilne.org/math/xnotes/AVs.pdf).
Thus `Z` remains isogenous to `E^n`: this is the closure-stability deduction.
For a minimal Galois closure, identify its function field with the normal
closure of `C(A)/C(X)`; do not identify a field closure with the global
scheme construction without that comparison.

A construction of members starts with a finite free group action on `A`
and forms `X=A/G`; the quotient/torsor existence is covered by
[Stacks, Tag 07S7](https://stacks.math.columbia.edu/tag/07S7).
Smoothness and projectivity of the intended quotient must be established
in its geometric implementation. A small proposed example uses `A=E^2`
and a nonzero `t in E[2]`, with involution `(x,y) -> (x+t,-y)`.
Its square is the identity and a fixed point would force `t=0`, so the
action is free. This example is already Galois; it tests a nontranslation
action, not a nontrivial passage to Galois closure.

If the target is itself abelian, a connected finite etale cover is already
an isogeny and Galois; its translation deck action is trivial on rational
Betti cohomology. The broader quotient class is therefore the useful
setting for the later deck-action comparison. Do not impose that the full
deck group fixes the chosen origin on `Z`. Branched or merely generically
finite covers do not have the same closure-stability argument.

#### Separate upstairs generation from trace descent

For `f:Y -> X` as above, let `d=deg(f)>0` and fix a rational Hodge class
`alpha` on `X` in degree `2p`. Pullback preserves its Hodge type. The
construction obligation is to produce `z in CH^p(Y)_Q` geometrically and
prove `cl_Y(z)=f^*alpha`. Once this is proved, descend by

\[
 z_X=\frac1d f_*z,\qquad
 \operatorname{cl}_X(z_X)
   =\frac1d f_*\operatorname{cl}_Y(z)
   =\frac1d f_*f^*\alpha=\alpha.
\]

The precise consumers are cycle-class compatibility with proper pushforward
and the Betti degree/trace identity. The cohomological projection formula
and cycle compatibility are recorded in
[Stacks, Tag 0FHA, Lemma 45.9.1 and condition (C)(b)](https://stacks.math.columbia.edu/tag/0FHA).
[Tag 02RH](https://stacks.math.columbia.edu/tag/02RH) is the finite-locally-free
degree identity on **cycles**; it is not itself a Betti realization theorem.
The displayed argument is a deduction from the genuine geometric laws,
not a completed Lean instance obtained by citing them.

Neither Galois closure nor a projector is needed for this descent identity.
After closure, the deck average can express invariant descent, with its
geometric action proved separately. Algebraicity comes from the upstairs
cycle construction, not from the averaging identity. Only representatives
of `f^*Hdg^p(X)` are needed, where `Hdg^p(X)` denotes rational Hodge classes
in degree `2p`; generation of every Hodge class on `Y` is a stronger,
unnecessary requirement.

In the optional elliptic-power-covered subclass, the cited divisor-generation
theorem supplies `z` as a combination of products of divisors on `A`.
This does not establish divisor generation on `X` itself.
Neither this descent nor averaging proves injectivity of the cycle map or
generation of the entire Chow group. The example does not supply a
reduction of all smooth projective targets to that subclass.

#### Assessed checkpoint: geometric properties behind upstairs generation

The comparison below records a concrete non-abelian example alongside the
other candidates, without changing the main smooth-projective target or
the immediate boundary-ideal checkpoint. These are geometric mechanisms,
not alternative definitions of Hodge membership.

| Property or proposed mechanism | Cycle recipe and independent image calculation | Decision |
| --- | --- | --- |
| Finite etale cover, normality or a Galois action alone | Pullback, transfer and averaging transport classes but do not supply their algebraic representatives | Retain as supporting operations, not a generation criterion. |
| Upstairs isogenous to a power of one elliptic curve | Divisor products; the cited elliptic-power Hodge theorem calculates their image | Keep the optional abelian-covered example. Do not extend the theorem to arbitrary abelian varieties. |
| Upstairs is a projective bundle over a smooth projective curve or surface | Relative hyperplane powers applied to cycles from the base; the Hodge-compatible bundle formula computes every coefficient | Keep as an optional deferred example. Low-dimensional base cycles are known independently, and the bundle presentation survives finite etale covers; implementation is not the immediate checkpoint. |
| Algebraic correspondences from other understood sources | Push--pull actual source cycles along explicitly constructed correspondences | Retain as a generalization. An abstract splitting or the label "Abelian type" supplies neither the correspondence cycles nor the required image calculation. |

The acceptance target is that the Betti image of the explicitly constructed
cycles contains `f^*Hdg^p(X)`. This is the equation to **prove**, not a
geometric hypothesis to assume. With the full Chow group in place of the
constructed cycles, the existence of such representatives is equivalent
to algebraicity downstairs, using pullback and normalized pushforward.
Thus packaging that existence condition does not resolve the construction.
For a direct route, make the same comparison on `X` without an auxiliary cover.

The optional projective-bundle construction, its exact scope and its first
implementation lemma follow. This preserves the comparison/design work,
not a completed Lean geometric instantiation or a selected next task.

#### Optional deferred construction: projective bundles over low-dimensional bases

Fix a smooth projective connected complex variety `X`. Supply a connected
finite etale surjection `f:Y -> X` of degree `d>0` and a projective-bundle
presentation `pi:Y=P_S(V) -> S`, where `S` is smooth projective connected,
`s=dim(S)<=2`, and `V` is locally free of rank `r>=1`.
The diagram and its different relative dimensions are

\[
 X\ \xleftarrow{\ f\ }\ Y=\mathbf P_S(\mathcal V)
   \ \xrightarrow{\ \pi\ }\ S,
 \qquad \dim X=\dim Y=s+r-1.
\]

The finite etale map `f` has relative dimension zero; `pi` is smooth
projective of relative dimension `r-1`. It is not another finite cover.
Use the quotient convention
`P_S(V)=Proj_S(Sym V)`, with `pi^*V ->> O_Y(1)`, as in
[Stacks, Tag 01OA](https://stacks.math.columbia.edu/tag/01OA).
Write `xi_CH` for the first Chern class operation of `O_Y(1)` on Chow
groups, and `xi_B=c_1^B(O_Y(1))` for its Betti class of type `(1,1)`.

**Precise classical conclusion:** for every `0<=p<=s+r-1`, every rational
Hodge class on `X` is represented by the degree-normalized pushforward of
a sum of `xi_CH^j` applied to pullbacks of cycles on `S`. The following
is a deduction from the cited classical results, not a new Hodge case.

For `J_p={j : 0<=j<r and 0<=p-j<=s}`, the bundle formula gives a unique
decomposition, respecting Hodge types,

\[
 f^*\alpha=\sum_{j\in J_p}\xi_B^j\cup\pi^*\beta_j,
 \qquad \beta_j\in\operatorname{Hdg}^{p-j}(S).
\]

The Chow formula is [Stacks, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX).
The same algebraic correspondences induce the motivic isomorphism in
[Tag 0FGQ](https://stacks.math.columbia.edu/tag/0FGQ); its Betti realization
gives the displayed decomposition. As Hodge structures, the summands of
`H_B^{2p}(Y)` are `H_B^{2(p-j)}(S)(-j)`. Thus the coefficients have type
`(p-j,p-j)`; an arbitrary rational vector-space splitting would not suffice.

The base representatives do not assume the desired conclusion for `X`:
in codimension zero use rational multiples of `[S]`; in codimension one
use divisors by [Lefschetz (1,1), Deligne section 2(iii)](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf);
and, when `s=2`, in codimension two use rational multiples of a closed
point, whose class generates top rational cohomology. These exhaust the
nonzero base codimensions. Choose such `z_j` with `cl_S(z_j)=beta_j` and set

\[
 z_Y=\sum_{j\in J_p}\xi_{\mathrm{CH}}^j\cap\pi^*z_j,
 \qquad z_X=\frac1d f_*z_Y.
\]

The construction's comparison to prove in Lean is

\[
 \operatorname{cl}_Y(\xi_{\mathrm{CH}}^j\cap\pi^*z_j)
   =\xi_B^j\cup\pi^*\operatorname{cl}_S(z_j).
\]

Together with the independently computed decomposition and the trace
square above, this gives `cl_X(z_X)=alpha`. Only flat pullback and iteration
of this line-bundle Chern operation are needed for the upstairs recipe;
a full correspondence algebra, new projector, or injectivity of the Chow
bundle map is not required for the forward class-generation argument.
For a higher-dimensional base the same decomposition remains valid, but
its coefficient classes require another generation argument.

**Galois-closure stability.** By
[Stacks, Tag 0BUM, Proposition 58.15.2](https://stacks.math.columbia.edu/tag/0BUM)
and the simple connectedness of projective-space fibers
([SGA 1, Expose XI, Proposition 1.1](https://arxiv.org/pdf/math/0206203)),
`pi_1^et(Y) -> pi_1^et(S)` is an isomorphism. Hence each connected finite
etale `Z -> Y` is `Y x_S S' -> Y` for a connected finite etale `S' -> S`.
Applying this to a Galois closure of `Y -> X` gives
`Z = P_{S'}(V|_{S'})`, with `S'` smooth projective of the same dimension.
This is a deduction from cover equivalence and bundle base change.
It does not say that `X` is itself a projective bundle, or that the full
deck group over `X` preserves the chosen fibration or hyperplane class.
Those equivariance statements require separate proofs if consumed; trace
descent of the constructed cycles does not require them.

#### Lean feasibility for optional examples

The audit uses Lean 4.24.0 and the pinned Mathlib revision
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; no dependency changes are proposed.

| Available construction | Missing comparison for the cover route or optional examples |
| --- | --- |
| `WeierstrassCurve.Affine.CoordinateRing` and `quotientXYIdealEquiv` in Mathlib's `EllipticCurve/Affine/Point.lean`; projective point/group APIs | Actual proper elliptic **scheme**, affine-chart and point-at-infinity identifications, and comparison of the ring fraction field with the scheme function field |
| Actual `Proj`, `Proj.basicOpenIsoSpec`, and properness in `ProjectiveSpectrum/Scheme.lean`, `ProjectiveSpectrum/Basic.lean` and `ProjectiveSpectrum/Proper.lean` | Specialization to the chosen homogeneous equation and proof of its curve properties; these do not follow from the point/group API |
| Existing actual graded cycles, principal relations and rational Chow quotient | Numerical degree of a divisor on a proper curve and degree zero of principal divisors; existing support-degree theorems concern dimension grading instead |
| Mathlib singular chain/homology functors; the project's actual finite-split singular `H^0` cycle comparison | Complex point topology/analytic comparison, genuine positive-degree Betti cohomology and the point-class/Hodge normalization; these were not found as ready-made adapters in the pinned sources |
| Field `IntermediateField.normalClosure`; affine normalization and deck-action maps in `Boundary/Normalization/` | Global finite etale Galois closure and its comparison to the field closure; abelian/isogeny stability is an additional obligation only for that optional example |
| Closed-immersion Chow pushforward; finite-discrete `H^0` transfer; conditional `RationalDegreeTransfer` | Finite-cover Chow pushforward with norm compatibility, and positive-degree Betti transfer with the actual cycle-class square and degree law |

#### PB0. Optional deferred scheme checkpoint

The pinned audit found no ready relative `Proj`, `P_S(V)`, scheme-level
`O(1)`/Chern operation, or projective-bundle Betti adapter. Do not introduce
a structure whose fields simply assume those comparisons. If this example
is resumed, start with the local geometry of a trivial rank-two bundle over
an affine base:

\[
 \bigl(R[X_0,X_1]_{X_0}\bigr)_0\ \cong_R\ R[T],
 \qquad X_1/X_0\longmapsto T.
\]

**First bounded lemma:** construct this algebra equivalence for an arbitrary
commutative ring `R`, using the total-degree grading, and prove its values
on constants and `X_1/X_0`. Prove both inverse identities, rather than
supplying a ring isomorphism as an input. Compose it with the existing
`Proj.basicOpenIsoSpec` to identify the literal scheme chart
`D_+(X_0)` with `Spec R[T]`, including the structural map to `Spec R`.
The degree-zero ring's identification with `R` must be explicit.

Use `MvPolynomial.homogeneousSubmodule`, `MvPolynomial.gradedAlgebra`
in Mathlib's `RingTheory/MvPolynomial/Homogeneous.lean`, and
`HomogeneousLocalization.Away`/`Away.mk` in
`RingTheory/GradedAlgebra/HomogeneousLocalization.lean`. The chart consumer
is the projection of the trivial projective-line bundle; later consumers
are its local hyperplane equation, overlap maps, and gluing for nontrivial
bundles. This is not a reintroduction of an elliptic-curve seed.

The separate later obligations are actual bundle gluing and `O(1)`,
flat Chow pullback and its Chern operation, the positive-degree Betti/Hodge
bundle comparison and base classes, and finite-cover trace compatibility.
Finite etale cover equivalence is needed only for the Galois branch.
Keep literature inputs explicit at use sites until implemented; this
checkpoint adds no Lean assumptions or declarations.

**Optional worked-example sequence, if selected:** use `E,p=1`
as the seed, then test `E^2,p=1`, and build toward the abelian-covered
subclass. A concrete seed proposal is the projective Weierstrass cubic
`y^2 z = x^3 - x z^2`, with its origin `[0:1:0]`; this fixes a model for
that example's implementation without restricting the main setting.
This seed has complex multiplication: the automorphism
`[i]:(x,y) -> (-x,i*y)` supplies an additional graph divisor for the `E^2`
test. Do not use a factors-plus-diagonal-only list for this chosen model.

For this optional sequence, the first bounded **geometry** checkpoint is
the actual projective curve, its affine-coordinate-ring chart and origin
as a closed point/support.
Require literal scheme maps/isomorphisms. Separate this from the subsequent
principal-degree-zero and `cl(D)=deg(D)cl([0])` checkpoints. The latter
requires independently constructed `H_B^2` and Hodge data, not a renamed
copy of `Q`. If the projective curve adapter first needs calibration, use
the `P^1` two-chart construction and the actual identity
`div(t)=[0]-[infinity]`; record that detour explicitly.

The optional subclass track then proves the displayed trace-descent laws
and its upstairs divisor generation. Global Galois closure is a separately
scoped cover checkpoint, not a prerequisite for trace descent. Do not treat finite-cover
norm descent or all positive-degree Betti theory as one small checkpoint,
and do not introduce a new abstract package merely to store these missing laws.

### G1. Fix a target and a non-circular construction before expanding APIs

If the selected construction uses an auxiliary cover/family, distinguish it
from the prescribed target `X`. Specify the maps between them, their degrees,
properness, variance and cohomological action where needed. Name the actual
Chow groups, Betti groups and cycle map; define Hodge membership independently.
Specify a correspondence algebra only if the chosen construction uses it.
State whether the checkpoint proves a known case, a selected projector's
action, or generation on a named Hodge subspace.

For a prescribed-class claim, fix `(X,p,α)` before choosing geometric data.
Write either a direct construction of a cycle with class `α`, or a geometric
construction of the comparison in section 3, identifying the still-unproved
equations `θ(a_H) = α` and the action square. Defining the target action to be
the constructed action, choosing a cycle representative of `α` as an input,
or simply supplying an arbitrary `α`-dependent linear map does not pass.

For a marked construction, prefer a geometrically constructed linear map
`r_CH : E_H → CH^p(X)_ℚ`, followed by `θ = cl ∘ r_CH`. If a Betti-side map
is constructed independently, prove that it agrees with this composite.
Then `θ(a_H) = α` supplies the actual representative `r_CH(a_H)`.
Constructing such a map for an arbitrary supplied `θ` is not automatic;
the coverage equation must still be proved. Keep `E_H` optional if a direct
geometric cycle construction suffices. Reuse `RationalHodgeCycleClassModel`;
this ordering requires neither a new abstract package nor a full motivic
category before the first example.

When using Scholl's projector for B, use the existing arbitrary
group-algebra-idempotent route (`Correspondence/GroupAlgebraProjector.lean`),
not silently identify a
character projector with a subgroup average. An automorphism-group action
is not by itself a finite étale Galois cover. If the marked Galois route is
required, construct and compare its actual cover/torsor and selector data.

**G1 acceptance:** one geometric diagram with typed maps, one precise target
statement, its source-hypothesis checklist, and a finite list of missing
lemmas with named consumers. A projector-image theorem alone does not pass
the separate arbitrary-Hodge-class generation gate.

### L1--L3. Bounded additive-localization stream

The next Lean checkpoint in the existing stream is L1. This stream can run
alongside G0/G1, but is a prerequisite for the selected application only if
that application's boundary-lifting argument uses it. Do not make general
localization a prerequisite for an independently constructed Chow projector.
The file names below are **prospective**, not existing implementations.

| Checkpoint | Exact result and reuse | Acceptance boundary |
| --- | --- | --- |
| L1. `Cycles/OpenClosedLocalization.lean` | Construct the reduced closed complement `i:Z → X` of `j:U → X`; prove `range(i_*) = ker(j^*)` on the existing raw and homogeneous cycles, using actual support/generic-point and coefficient identities. | Any coefficient semiring; canonical restrictions of the supplied dimension function; no Noetherian premise. Include empty/full opens, trivial coefficients and nonreduced ambient schemes. A complementary-pair lemma must be instantiated by the actual complement. |
| L2. `Cycles/PrincipalRelationLifting.lean` | Extend an open principal-relation carrier by reduced closure and its function by the inverse of the actual open function-field equivalence. Prove integral and rational relation-span image equalities using SP61 and coefficient compatibility. | Keep carrier degree `m+1`, exact function-field variance and representative identities. Data lifting needs no ambient finiteness; actual relation spans retain target Noetherianity. The lifted divisor may acquire boundary terms: this is not a relation-preserving closure section. |
| L3. `Cycles/ChowLocalization.lean` | Correct a cycle representative by a lifted principal relation, apply L1, and descend to integral/rational quotient kernel=image; reuse SP63 surjectivity. | Prove the right-exact sequence on the actual existing maps. Derive finiteness of the open and closed sources from the Noetherian target. Do not assume rationalization injective or closed Chow pushforward injective. |

After L3, stop generic expansion until G1 identifies the next consumer.
An adapter to `Inputs/ChowLocalization.lean` is appropriate only for these
exact maps and an identified use; do not add a blanket source instance or
another abstract quotient. Additive exactness is not multiplicativity of
correspondence restriction, and boundary support is not defect vanishing.

### G2--G4. Construct only what the selected geometry needs

**G2: actual cycle map and operations.** Construct the selected Chow--Betti
model: define the Betti class of actual cycles, prove it kills the existing
principal relations, descend to the existing Chow quotient, and prove its
image lies in the independently specified Hodge subspace. Add a
correspondence action or Tate-block detection only if the chosen route uses
it. Prove only the proper/flat/intersection/composition laws needed by the G1
diagram. Use the existing quotient and grading; any new operation must have
a named consumer. A graph-generated subalgebra result must not be presented
as a map on the full finite-étale span algebra without the additional proof.

**G3: optional chosen-projector and extension branch.** Compare three possible
mechanisms for the selected family, rather than require all three:

- construct the required Chow correspondence/projector directly;
- apply the precisely matched Abelian-type extension result to an existing
  Chow idempotent, with its realization comparison;
- use raw Chow lifting and separately prove a correction or vanishing of
  its idempotence defect.

Neither extension existence nor a cited realization theorem supplies the
inertia if-and-only-if in `CompactifiedSubgroupProjectorExtension`. Use an
appropriately weaker existing interface when sufficient. Cover extension,
deck-action extension and Chow-projector extension remain separate tasks.
Construct the desired action on the independently fixed target.

**G4: class coverage, then any generalization.** A direct cycle construction
can reach this checkpoint without G3. Prove that the geometric
construction works for each class in the selected Hodge subspace. A
universal conclusion additionally needs all codimensions and all smooth
projective complex targets, or a proved reduction covering them. No
reduction to Abelian-type geometry is currently available in this repository.
The stronger reverse Galois equivalence retains its separate replacement
or factorization obligation; it is not required for the forward implication.

Keep the minimal endpoint minimal: lower-left class extraction needs
detection and the marked action/class equations, not residual surjectivity
or idempotence. Those stronger conditions serve the full chosen-projector
conclusion. Do not force the residual map to be multiplicative: the proved
`MultiplicativeResidualRigidity` result forces its generated class to `-1`
when it is multiplicative and surjective, so that specialization cannot
provide variable-class coverage.

### Working and release rules

- Keep current planning and unresolved comparisons here and in `GAP_MAP.md`,
  not as editorial gap/status paragraphs in the manuscript. Reuse the one
  manuscript and existing notation; do not create a second active plan.
- Distinguish a cited mathematical theorem from its Lean implementation.
  Exact literature input packages stay explicit in the consuming theorem
  signatures until proved. No project axioms, `sorry` or `native_decide` in
  proved endpoints; preserve the intentional Challenge placeholders.
- Before implementation, record each candidate's first unsupported arrow.
  If an input merely restates class generation or the required action,
  return to G1 rather than count packaging as proof progress.
- Review new objects against the parity registry before adding wrappers.
  Promote a proved checkpoint only after the appropriate build, focused
  regressions, dependency/axiom checks and Lean--TeX comparison.
- **Next action:** prove compatibility of B4n's actual affine normalized
  covers, structural maps and marked refinements under localization and
  on overlaps. Then establish cocycle identities, gluing and the
  compatible global Galois action. The construction needs no
  Noetherianity premise and bypasses the proposed whole-source
  integral-closedness route; it does not establish that stronger result.
  B4j constructs the finite etale tensor
  source and its actual integral/generic evaluations, with generic
  surjectivity and quotient identification proved from normal closure.
  B4i has removed the separately
  supplied second finite normal algebra and constructs the existing cover
  from an actual affine inverse image and its marked generic extension.
  Normal stalks from smooth geometry and the global finite etale Galois
  refinement remain separate tasks. B4d already derives the finite/etale affine rings
  from a supplied finite morphism and proves the normalization
  identification over the original base. Full visibility is constructed on this branch,
  not added to every `NormalizedCover`. Retain nonempty-boundary geometry
  as an alternative if needed. Preserve PB0 and the abelian examples as
  optional deferred work, with the general smooth-projective target unchanged.
  L1 remains the next checkpoint of the separate bounded localization
  stream, only if continued in parallel for a named consumer. No new
  geometric family is implemented or universal reduction asserted here.

## 1. Fix the target before choosing a cover

For a smooth projective complex variety \(X\) and codimension \(p\), put
\(A=\mathrm{CH}^p(X)_{\mathbb Q}\), \(V=H^{2p}(X,\mathbb Q)\), and let
\(V_{\mathrm{Hdg}}\) be the inverse image of \(H^{p,p}(X)\) under
complexification. The intended statement is

\[
  \mathrm{HC}_{\mathbb Q}(X,p):\quad
  \forall\alpha\in V_{\mathrm{Hdg}},\quad
  \exists z\in A,\quad \operatorname{cl}(z)=\alpha.
\]

Hodge membership is specified independently of the cycle-class image.
Write \(\mathscr H=(A,V,V_{\mathrm{Hdg}},\operatorname{cl})\) for these data.
`RationalHodgeCycleClassModel` and `RationalHodgeConjectureAt` in
[`HodgeClasses.lean`](../HodgeConjecture/Realization/HodgeClasses.lean)
record this logical shape. To get the classical universal conjecture, the
family index must cover all smooth projective complex varieties, all
codimensions must be included, and the supplied models must be their actual
geometric data. Those general instances are not constructed here.

## 2. The equivalence already proved in Lean

Fix a rational algebra \(\Gamma\) and action
\(\rho:\Gamma\to\operatorname{End}_{\mathbb Q}(\mathbb Q\oplus V)\).
Geometrically, the marked rational line has Tate type \(\mathbb Q(-p)\);
Lean's block calculation uses its underlying rational module. The required
graded/twisted Chow realization and variance conventions must be justified
in a general instance, not inferred from the block notation.

Define \(P_\alpha(t,x)=(t,t\alpha)\) and
\(d_{\mathrm{ll}}(T)=\operatorname{pr}_V(T(1,0))\). Supply:

- **Construction** \(C:A\to\Gamma\), with \(C(z)^2=C(z)\) and
  \(\rho(C(z))=P_{\operatorname{cl}(z)}\). This is a function, not a
  claimed linear map: its formula includes the marked identity block.
- **Detection** \(D:\Gamma\to_{\mathbb Q} A\), with
  \(\operatorname{cl}(D(\gamma))=d_{\mathrm{ll}}(\rho(\gamma))\).

Then the checked bridge is

\[
  \mathrm{HC}_{\mathbb Q}(\mathscr H)
  \quad\Longleftrightarrow\quad
  \forall\alpha\in V_{\mathrm{Hdg}},\quad
  \exists\Pi\in\Gamma,\quad \Pi^2=\Pi,\quad\rho(\Pi)=P_\alpha.
\]

The forward direction takes \(\Pi=C(z)\) from a cycle representative.
The reverse direction takes \(z=D(\Pi)\). Thus construction is needed for
the forward reformulation; detection alone suffices to turn independently
constructed lifts into the Hodge conclusion. Idempotence of \(P_\alpha\)
holds for every vector and does not itself construct an algebraic lift.

Equivalently, for \(\mathcal U=\mathbb Q\times\mathbb Q\) and
\(\varphi_e(r,s)=re+s(1-e)\), require an idempotent \(\Pi\) with
\(\rho\circ\varphi_\Pi=\varphi_{P_\alpha}\). This is the same target,
not an additional conjecture.

The exact declarations are
`rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift` and
`rationalHodgeConjectureAt_iff_everyHodgeClassHasPalomarTargetSquare` in
[`TateGraphProjector.lean`](../HodgeConjecture/Realization/Chow/TateGraphProjector.lean).
The Hodge-morphism presentation additionally uses
`ClassGraphProjectorHodgeCompatibility`; it is unnecessary when membership
in the independently specified Hodge subspace is used directly.

## 3. Minimal marked route to a prescribed class

Fix \(\alpha\) first. For a marked augmented algebra with selector \(q_H\),
residual ideal \(E_H\), and \(a_H=q_H-1\), seek actual geometric data
\(\Pi\in\Gamma\), \(\theta:E_H\to_{\mathbb Q}V\) satisfying

\[
  \theta(a_H)=\alpha,\qquad
  \rho(\Pi)\Theta=\Theta P_{a_H},\qquad
  \Theta=\operatorname{id}_{\mathbb Q}\oplus\theta.
\]

Evaluating at \((1,0)\) gives the entire needed implication:

\[
  \operatorname{cl}(D(\Pi))
    =d_{\mathrm{ll}}(\rho(\Pi))
    =\theta(a_H)=\alpha.
\]

The operator lemma is
`MarkedProjectorActionComparison.lowerLeftClass_action_eq_generatedClass`;
the Chow bridge is `cycleClass_decode_eq_generatedClass`, with detection
explicit in its signature, both
in [`MarkedAugmentedRealization.lean`](../HodgeConjecture/Realization/Chow/MarkedAugmentedRealization.lean).
This lower-left conclusion does not need surjectivity or idempotence.
Idempotence of \(\Pi\) and surjectivity of \(\theta\) additionally give
the full graph-projector lift and the universal-algebra target square.
Do not impose these stronger requirements just to extract one cycle class.

The marked proof spine follows one chosen algebraic projector \(\Pi\) for
each prescribed \(\alpha\), with its extension data retained:

| Conclusion | Inputs beyond the marked comparison and prescribed-class equality | Lean location |
| --- | --- | --- |
| A cycle \(z=D(\Pi)\) with \(\operatorname{cl}(z)=\alpha\) | Detection | Core `cycleClass_decode_eq_generatedClass` |
| The chosen \(\Pi\) as a full graph lift | Its idempotence and residual surjectivity for this cancellation proof | Core `toAlgebraicProjectorLift`; extension specialization uses \(\Pi=\Pi_x\) for the chosen witness \(x\) |
| Reverse implication from the Hodge target to the existing marked Galois coverage | Construction and the named replacement hypothesis | `classDependentMarkedGaloisSelectorCoverage_of_everyHodgeClassHasGraphProjectorLift` |

The projector-lift conclusion keeps exactly the chosen element. Its
extension data and witness \(x\) must remain available separately, since
an ordinary `AlgebraicProjectorLift` does not store them. A genuine geometric
extension instance remains to be constructed in the general setting.
Construction \(C\) is retained for the Hodge-to-graph direction of the
equivalence, not as a second projector in the marked construction.

The Galois replacement hypothesis asserts existence of some structured
witness for the same class, not equality with a particular input projector.
It is not an identity-preserving conversion. The full Galois equivalence
therefore retains an additional obligation beyond the graph equivalence.

The chosen algebra, maps, and action square must come from geometry. In
particular, choosing a Chow representative of \(\alpha\) to build them
would assume the desired conclusion. If a geometric factorization
\(\theta=\operatorname{cl}\circ r_{\mathrm{CH}}\) is constructed and
\(\theta(a_H)=\alpha\) is proved, then \(r_{\mathrm{CH}}(a_H)\) already
is the requested cycle; no further operator argument is necessary.

## 4. Where actual construction is missing

| Obligation | Present status | Exact task |
| --- | --- | --- |
| Genuine target and block detection | Constructed for finite split degree zero | Construct the general geometric model, correspondence action, and detection law; construct the encoding for the full equivalence |
| Class-dependent geometric generation | Canonical marked example gives \(-\operatorname{cl}[Z_I]\) | For a prescribed Hodge \(\alpha\), build genuine data and prove \(\theta(a_H)=\alpha\), without assuming its algebraicity |
| Geometric action comparison | Constructed for that finite split example | Prove the displayed action square for the newly constructed data |
| Extension, when the chosen construction needs a boundary | Local fixed-ring results and conditional input consumers; actual graph/cycle geometry and surjective integral/rational Chow restriction | Follow G1/G3 for the selected family: prove the needed extension and action comparisons. L1--L3 supply additive localization for a boundary-lifting route; direct graph projectors or a matched motivic extension can use a different dependency path. |
| All-class and universal quantifiers | Abstract schemas only beyond the finite case | Make the construction work for every prescribed class in every intended geometric model |

The finite split target itself has graph lifts for every degree-zero class;
the canonical marked Galois construction is the narrower fixed-class result.
Its residual map is an actual equivalence, not a lossy projection.

The commutative-algebra localization branch concerns local rings, fixed
rings, and inertia. It feeds the extension obligation only after the geometric
comparison and global extension hypotheses have been justified. For a raw
lift \(\Pi_0\) of a generic idempotent, Chow localization places
\(\Pi_0^2-\Pi_0\) in a boundary image, given a separately justified
algebra restriction and exactness for that same map. Boundary support is
not defect vanishing.
Neither conclusion supplies the prescribed-class action square by itself.

The stronger existing Galois coverage schemas retain additional extension
data. Their converses require named replacement/factorization hypotheses.
Those hypotheses are not needed for the forward Hodge implication and are
not part of the basic graph-projector equivalence.

## 5. Bench and earlier validation

The standalone matrix-restriction diagnostic is preserved on the
[object bench](bench/README.md), outside active imports and manuscript claims.
It is not an obstruction assumed by this sketch. No choice of \(\Gamma\)
as a full matrix algebra, and no ambient restriction to commutative sheets,
is required by the core action comparison. Actual finite Chow matrix
coordinates remain where their verified constructions use them.

At the preceding bench/reorganization checkpoint, the full Lean build,
all 100 active axiom reports, the proof-dependency
audit, and the single manuscript PDF build passed after the bench move.
The two chosen-projector regression checks retain the original element and
its supplied restriction law; the auxiliary bench source also checks
separately. These checks concern the statements and their placement, not
geometric instances of the obligations in the table above.

## 6. Construction inventory and detailed dependencies

Keep the existing target equivalence fixed. The correspondence route below
works toward its geometric instance, with one chosen projector for each
prescribed class; a direct Chow--Betti class construction need not use that
route. The closed-graph/restriction checkpoint is constructed at scheme
level, and integral graph generators now have finite-cycle and
open-restriction maps.
Their composition intersection and image are identified as actual schemes;
integral fundamental multiplicity is computed over the ambient stalk.
The class-generation theorem is a separate mathematical obligation and must
be developed alongside that infrastructure.
The operative next actions and family-selection gate are in section 0;
the dated checkpoints below document how the existing objects were built.

1. **Closed graph subschemes and open restriction: scheme-level checkpoint
   constructed.** For a separated structural morphism,
   [`GraphSubscheme.lean`](../HodgeConjecture/Correspondence/GraphSubscheme.lean)
   constructs `graphMorphism`, its kernel `graphIdeal`, and
   `graphSubschemeIso`. The graph is a closed immersion and hence proper as
   a morphism to the relative product. Given an actual finite étale
   extension `E` over an open \(j:U\hookrightarrow S\), with inclusion
   \(\iota:Y\to\bar Y\),
   [`GraphRestriction.lean`](../HodgeConjecture/Boundary/GraphRestriction.lean)
   constructs the open pair inclusion \(\iota^{(2)}\), proves
   `graphRestriction_isPullback`, and proves the actual ideal equality
   \[
     \mathcal I_{\sigma_U}
       =(\iota^{(2)})^*\mathcal I_\sigma
   \]
   in `graphIdeal_restriction`, where \(\sigma_U=E.\mathrm{restriction}(\sigma)\).
   Here the graph morphism is \(g_\sigma=(\mathrm{id},\sigma)\), its closed
   subscheme is \(\operatorname{Gr}(\sigma)\), and \(\mathcal I_\sigma\)
   is its defining ideal; inverse image is `IdealSheafData.comap`.
   Restricting an already extended automorphism needs no
   `DeckExtensionHypothesis`. The corollary `graphIdeal_liftDeckAction`
   uses that explicit hypothesis only to lift a prescribed original action.
   **Established:** actual schemes, closed immersions, and scheme-theoretic
   base change, without finite point labels. Constructing the extension in
   the intended geometric application remains a separate input obligation.

2. **Cycle assembly and open restriction, then the correspondence algebra.**
   `Cycles/Basic.lean` defines finite, ungraded cycles on actual integral
   ideal-sheaf subschemes; the earlier finite split cycle types reuse this
   definition. `Cycles/OpenRestriction.lean` restricts each integral
   generator by actual ideal-sheaf inverse image, returning zero for an
   empty intersection. A nonempty inverse image is proved integral.
   `Correspondence/GraphCycles.lean` makes an integral source's closed graph
   into such a generator, proves its dimension agrees with the source via
   the graph isomorphism, and linearly assembles rational graph sums.
   `Boundary/GraphCycleRestriction.lean` connects these constructions to
   the supplied extension: restriction commutes with graph-cycle assembly
   and with the induced rational deck-group map. The nonempty original
   cover is integral because it is open in the integral extended cover.
   These are cycle-level statements, not a Chow algebra or its realization.

   **Remaining correspondence-layer obligation:** the general dimension
   functions, actual integral/rational Chow quotients and open maps are now
   constructed below. For the theory selected at G1, prove diagonal,
   composition, and multiplicative restriction compatibility using its
   required geometric operations. Specify the admissible relative or support-controlled
   algebra on which restriction is multiplicative; do not assume this for
   every absolute correspondence. Aim to instantiate
   `CompactifiedDeckGraphComparison` in
   [`CompactifiedGraphProjector.lean`](../HodgeConjecture/Boundary/CompactifiedGraphProjector.lean).
   Its current fields require cycle maps on the indicated full finite-étale
   span algebras; a graph-generator construction alone must not be reported
   as an instance of that stronger interface. **Acceptance:** actual cycle
   maps and a proved restriction square on the stated source, yielding
   idempotence of the chosen group-algebra image. If the graph route cannot
   be realized, separately assess raw closure and defect correction;
   boundary support alone is insufficient.

   Retain the raw cycle module beneath the constructed homogeneous
   submodules for a supplied dimension function. An open subset need not
   preserve absolute Krull dimension; the proved grading uses the literal
   restricted function instead. Graphs with nonintegral carriers also need actual
   component cycles and multiplicities, not an assumed coefficient-one
   formula. In particular, finite étaleness alone does not make the base or
   cover reduced. The cycle-restriction proof introduces neither a Chow
   quotient by chosen equations nor an assumed convolution law.

   **Scheme-theoretic composition checkpoint:**
   `Correspondence/GraphComposition.lean` realizes the relative triple
   product as the fiber product of the two relative pairs over their middle
   coordinate. The actual ideal
   \[
     \mathcal J_{\sigma,\tau}
       =p_{12}^*\mathcal I_\tau+p_{23}^*\mathcal I_\sigma
   \]
   defines an intersection isomorphic to the source by
   \(y\mapsto(y,\tau y,\sigma(\tau y))\). Its first/last projection
   is isomorphic onto \(\operatorname{Gr}(\sigma\tau)\), with equality
   of scheme-theoretic image ideals. Only separatedness is used; no
   commutativity of the deck group is assumed.
   `Cycles/IntegralMultiplicity.lean` separately proves that an integral
   closed subscheme has generic stalk length one over the **ambient** stalk,
   using its actual closed-immersion stalk map. This is the coefficient in
   the integral fundamental cycle, not a Chow intersection multiplicity law.

   **Graph-slice cycle pull–push checkpoint:** `Cycles/ClosedImmersionPushforward.lean`
   constructs actual integral image supports and degree-one image cycles;
   the global closed-immersion map is linear and functorial. The generic
   residue-degree proof is now canonical in `Cycles/ResidueDegree.lean`,
   with the older split-point name retained as an adapter. For
   \(W=Y\times_S Y\), `Correspondence/GraphSlice.lean` constructs
   \(s_\tau:W\to T\), \((y,z)\mapsto(y,\tau y,z)\), identifies its
   image with \(p_{12}^{-1}\operatorname{Gr}(\tau)\), and proves that
   \(u_\tau=p_{23}s_\tau\) is the pair isomorphism \((\tau,\mathrm{id})\).
   The actual cycle maps in `GraphCycleComposition.lean` satisfy
   \[
     \mathsf R_\tau[\operatorname{Gr}(\sigma)]
       =[\operatorname{Gr}(\sigma\tau)],\qquad
     \mathsf K_\tau[\operatorname{Gr}(\sigma)]=[Z_{\sigma,\tau}],
   \]
   where \(\mathsf R_\tau=u_\tau^*{}_{\mathrm{cyc}}\) and
   \(\mathsf K_\tau=s_{\tau,*\mathrm{cyc}}\mathsf R_\tau\).
   The supportwise outer image of \([Z_{\sigma,\tau}]\) is
   \([\operatorname{Gr}(\sigma\tau)]\), with its actual residue degree one.
   The first two maps extend linearly. No integral generator is assigned
   to either possibly reducible inverse-image graph subscheme.
   Étaleness makes these graph and slice inclusions open as well as closed.

   **Structural-base comparison checkpoint (A11s / SP34):** for
   \(p:Y\to S\), \(b:S\to B\), \(r=b\circ p\),
   `DeckBaseChange.lean` retains the actual automorphism through an
   injective group homomorphism, denoted \(\sigma\mapsto\bar\sigma\).
   `RelativeProductComparison.lean` constructs closed pair and triple
   inclusions \(\kappa_2:W_p\to W_r\), \(\kappa_3:T_p\to T_r\)
   when \(b\) is separated. `GraphBaseComparison.lean` proves actual
   morphism, graph-image, and intersection-image compatibility.
   `GraphCycleBaseComparison.lean` proves
   \[
     \kappa_{2,*\mathrm{cyc}}[\operatorname{Gr}_p(\sigma)]
        =[\operatorname{Gr}_r(\bar\sigma)],\qquad
     \kappa_{3,*\mathrm{cyc}}[Z^p_{\sigma,\tau}]
        =[Z^r_{\bar\sigma,\bar\tau}],
   \]
   with separated \(p,b\) and integral \(Y\), including the rational
   weighted graph-assembly square. On all finite cycles the comparison
   pushforwards also intertwine \(\mathsf R\) and \(\mathsf K\),
   without an integrality premise. `Cycles/IsomorphismTransport.lean`
   proves this through genuine isomorphism pullback and inverse closed
   pushforward. For \(B=\operatorname{Spec}k\), the destination pair
   and triple are the absolute products; their cycle comparison is now
   constructed, not merely a proposed identification.

   **Local coefficient checkpoint (A11t / SP35):** `Cycles/LocalOrder.lean`
   uses the existing quotient-length order on fraction fields, restricted
   to units, to obtain signed integers. It proves finite quotient lengths,
   numerator-minus-denominator, product/inverse laws, and vanishing for
   local units. `LocalOrderTransport.lean` proves ring/field-isomorphism
   invariance. `FunctionFieldTransport.lean` constructs the actual
   contravariant function-field map of a scheme isomorphism and its square
   with each stalk map. `SchemeLocalOrder.lean` constructs the point index
   \(\operatorname{DivPt}(X)=\{x:\dim\mathcal O_{X,x}=1\}\), including
   points obtained from height-one primes in an affine chart, and proves
   \(\operatorname{ord}_x(e^*f)=\operatorname{ord}_{e_1(x)}(f)\).
   The scheme-order construction needs integral locally Noetherian schemes,
   not normality or DVRs. This checkpoint proves the actual local
   coefficients; the principal-divisor cycle is assembled in A11w / SP38.

   **Closed support checkpoint (A11u / SP36):** `Cycles/PointSupport.lean`
   constructs the actual reduced closure \(Z_x\) of every scheme point,
   with inverse \(\xi_Z=\iota_Z(\eta_Z)\) on the existing integral
   ideal-sheaf subschemes. `SupportCodimension.lean` identifies chain
   codimension with the dimension of the actual local ring.
   `DivisorSupport.lean` restricts the equivalence to
   \(\operatorname{DivPt}(X)\simeq\operatorname{PrimeDiv}(X)\), where
   prime divisors are a subtype of the existing cycle generators.
   Its isomorphism transport is proved equal to the existing ideal-sheaf
   image, and the signed local-order comparison holds on these supports.
   This identification needs no integral or Noetherian ambient hypothesis;
   the local coefficients retain their integral locally Noetherian domain.

   **Finiteness checkpoint (A11v / SP37):** `Cycles/HeightOneFiniteness.lean`
   proves that height-one primes containing a nonzero element are minimal
   over its principal ideal and form a finite set in a Noetherian domain
   of arbitrary dimension. `RationalFunctionPresentation.lean` expresses
   each actual rational function by nonzero sections on any nonempty affine
   chart and proves that its coefficient vanishes where both germs are
   units. `DivisorFiniteness.lean` gives a finite affine bound and uses the
   generic-point/open-set equivalence to prove local finiteness of the
   actual closed supports. Quasi-compactness then gives finite support in
   both the existing point and prime-divisor presentations. No normality,
   properness, or finiteness of the whole prime-divisor index is assumed.

   **Principal-divisor checkpoint (A11w / SP38):**
   `Cycles/PrincipalDivisor.lean` assembles the finite sum in the existing
   `Cycles X ℤ`, with the existing local order at prime divisors and zero
   elsewhere. It proves its exact support and product/inverse/quotient
   laws, and bundles the multiplicative-to-additive homomorphism.
   `IsomorphismTransport.lean` identifies the existing pushforward with
   reindexing through actual image supports. `PrincipalDivisorTransport.lean`
   proves both pushforward and existing open-restriction identities through
   a scheme isomorphism and its actual contravariant function-field map.
   Integral locally Noetherian quasi-compact hypotheses are explicit;
   no relation package or new cycle module is supplied.

   **Dimension-function checkpoint (A11x / SP39):**
   `Cycles/DimensionFunction.lean` retains both conditions of the standard
   dimension-function definition on actual points. Support degree is
   \(\delta(\xi_Z)\); prime codimension implies immediate specialization
   and hence degree \(\delta(\eta)-1\).
   `DimensionFunctionRestriction.lean` constructs actual closed-immersion
   restriction and proves degree agreement with the actual closed image.
   `CycleDegree.lean` selects homogeneous submodules of the existing cycles,
   not another free module. `PrincipalDivisorDegree.lean` proves the
   principal cycle homogeneous and shows that pushing from an integral
   closed carrier \(W\) gives ambient degree \(\deg_\delta(W)-1\).
   Only that carrier needs local Noetherianity and quasi-compactness;
   the ambient scheme need not be integral. The dimension function remains
   an explicit parameter, not a theorem of existence for every scheme.

   **Principal-relation checkpoint (A11y / SP40):** on Noetherian schemes
   with an explicit dimension function, `PrincipalRelations.lean`
   generates relations from actual degree-\(n+1\) integral carriers
   and their function-field units. Span membership is equivalent to an
   unweighted finite sum of actual ambient principal cycles, using powers
   to absorb integer coefficients. Locally finite **carrier** families
   are finite on the chosen quasi-compact domain, even when their
   principal cycles vanish, so the finite relation convention matches
   the source. The resulting quotient is \(\mathrm{CH}_n^\delta\).
   `PrincipalDivisorImage.lean` transports each principal image through
   the actual closed support-to-image function-field isomorphism;
   `GradedPushforward.lean` restricts the existing geometric cycle map.
   `ChowPushforward.lean` proves generator and submodule preservation,
   then quotient descent, the representative square and identity/composition.
   `ChowIsomorphism.lean` gives the actual quotient isomorphism, whose
   inverse on cycles is the existing open restriction along the isomorphism.
   Actual dimension-function restriction discharges the degree comparison;
   no freely chosen relation submodule or relation-preservation premise is used.

   **Geometric-dimension checkpoint (A11z / SP41):**
   `SupportDimension.lean` proves that an actual integral carrier has
   dimension equal to the height of its ambient generic point. On a
   finite-dimensional scheme, point-closure height is a finite integer
   and strictly increases along proper generization.
   `FiniteTypeDimension.lean` proves a finite polynomial-presentation
   bound and finite dimension for finite-type algebras over a field;
   `FiniteTypeSchemeDimension.lean` extends this to actual finite-type
   schemes using a finite affine subcover and the stalk-isomorphism
   comparison for point coheight. Neither an exact polynomial dimension
   formula nor a dimension-function law is assumed.
   `LowDimensionalDimensionFunction.lean` constructs the actual
   \(\delta_X(x)=\dim\overline{\{x\}}\) when \(\dim X\leq1\),
   proving both laws from the dimension bound and identifying the existing
   support degree with actual carrier dimension. The affine-line example
   has dimension one, generic-point degree one and origin degree zero.
   This supplies a genuine bounded grading instance for SP40, not the
   general finite-type dimension-function construction.

   **Affine-dimension checkpoint (A11aa / SP42):**
   `TranscendenceDegreeDrop.lean` proves strict drop under actual
   noninjective surjections of domains with finite transcendence degree.
   Applied to prime quotients, this gives a prime-chain upper bound.
   `IntegralDimension.lean` proves dimension invariance using actual
   contraction and chain lifting; `NormalizationDimension.lean` uses
   Noether normalization and the proved polynomial lower bound for the
   independent opposite inequality. `AffineDimension.lean` therefore
   proves \(\dim A=\operatorname{trdeg}_k\operatorname{Frac}(A)\)
   for finite-type domains, and the sharp field-polynomial dimension
   formula. `AffineSupportDimension.lean` identifies the dimension of
   the existing actual reduced carrier of a point of
   \(\operatorname{Spec}A\) with \(\operatorname{trdeg}_k\kappa(p)\),
   where \(\kappa(p)\) is the actual prime-localization residue field.
   This last result allows reducible ambient algebras and also identifies
   the integer scheme-point height. No immediate-specialization law or
   dimension-function package is supplied as a hypothesis.

   **Polynomial-local checkpoint (A11ab / SP43):**
   `PolynomialPrimeHeight.lean` constructs prime extension along the actual
   constant-polynomial map, proves contraction recovers the original prime,
   and proves the extended contraction is strictly below any maximal ideal.
   This gives \(\operatorname{ht}(m\cap R)+1\leq\operatorname{ht}(m)\)
   for every commutative ring. `PolynomialMaximalHeight.lean` combines
   Jacobson maximal contraction, variable induction and SP42's independent
   upper bound to prove
   \(\operatorname{ht}(m)=\dim k[T_1,\ldots,T_n]_m=n\) for every maximal
   ideal over any field, including \(n=0\). No rational-point assumption is
   needed. `PolynomialClosedPointDimension.lean` identifies the actual
   closed-point stalk dimension and scheme-point coheight with \(n\).
   This is not the closed carrier's dimension, which is zero, and does not
   claim regularity, generators or uniform saturated-chain lengths.

   **Normal-base/local-dimension checkpoint (A11ac / SP44):**
   `IntegralIdealPolynomial.lean` constructs ideal-controlled monic
   annihilators in any integral algebra, using an actual finite integral
   subalgebra. `MonicPrimeCoefficients.lean` controls monic-divisor
   coefficients after reduction modulo a prime and scalar substitution.
   `NormalGoingDown.lean` uses actual minimal polynomials to prove
   cancellation, then constructs a prime below the prescribed terminal
   prime. Thus integral injections of domains over an integrally closed
   base have going down, with no separability, Noetherianity or
   target-normality premise and no assumed going-down input.
   `NormalizationLocalDimension.lean` reuses the existing going-down
   height bound and integral incomparability to compare actual heights.
   Polynomial-base normality and SP43's maximal heights give
   \(\operatorname{ht}(m)=s\) through an actual polynomial normalization.
   Every finite-type domain therefore satisfies
   \(\dim A_m=\dim A=\operatorname{trdeg}_k\operatorname{Frac}(A)\)
   at every maximal ideal. `AffineClosedPointDimension.lean` identifies
   actual closed-point stalk dimensions and scheme-point coheights.
   Neither normality of \(A\) nor rationality of the closed point is needed.
   Integrality of the selected local-ring map is not assumed.

   **Residue-localization checkpoint (A11ad / SP45):**
   `ResidueNormalizationLift.lean` lifts an actual polynomial normalization
   of \(B/q\) through the quotient map, with an exact commuting square
   and denominators disjoint from \(q\). `GenericFiberAlgebra.lean`
   constructs the canonical \(K=\operatorname{Frac}(P)\)-algebra on
   \(B'=f(P\setminus\{0\})^{-1}B\), with scalar compatibility and
   finite type from the actual localization pushout.
   `ResidueLocalization.lean` proves the extended prime \(q'\) maximal
   via the actual localized quotient field and its exact kernel. It also
   proves contraction to \(q\) and unchanged height; these comparisons
   do not need integrality. `ResidueNormalizationLocalization.lean`
   supplies the full existential construction for any finite-type algebra,
   without requiring the ambient ring to be a domain. For domain \(B\),
   SP44 further gives \(\operatorname{ht}_B(q)=\operatorname{trdeg}_K B'\).
   Integrality concerns \(P\to B/q\), not the lifted \(P\to B\).

   **Original-field prime-formula checkpoint (A11ae / SP46):**
   `LocalizationTranscendenceDegree.lean` proves full cardinal invariance
   under actual domain localization, with universe-general and numeric
   forms and no finite-type assumption. `AffinePrimeDimension.lean`
   combines that comparison with the canonical polynomial fraction-field
   tower to prove \(n+\operatorname{trdeg}_K B'=\operatorname{trdeg}_k B\).
   The rational function field's finite transcendence degree comes from \(n\), not
   from a false finite-type hypothesis over \(k\). SP45 and the actual
   quotient normalization now give
   \(\operatorname{ht}_B(q)+\operatorname{trdeg}_k(B/q)=\operatorname{trdeg}_k B\)
   for every prime of a finite-type domain. Ordinary height, the actual
   prime-localization residue field, quotient dimension, and the actual
   local-ring formula \(\dim B_q+\dim(B/q)=\dim B\) are also proved.
   No normality, rationality, characteristic-zero or maximality premise
   is added. The domain condition on this global formula is explicit.

   **Consecutive-prime checkpoint (A11af / SP47):**
   `PrimeQuotientCover.lean` transports a prime-spectrum cover
   \(p\lessdot q\) through the actual quotient correspondence,
   proving \(0\lessdot q/p\) and \(\operatorname{ht}_{B/p}(q/p)=1\)
   over any commutative ring. No domain or Noetherianity of \(B\)
   is assumed, and the cover is not taken in the full ideal lattice.
   `ConsecutivePrimeDimension.lean` applies SP46 to \(B/p\) and the
   actual double-quotient \(k\)-algebra equivalence, giving
   \(\operatorname{trdeg}_k(B/q)+1=\operatorname{trdeg}_k(B/p)\).
   The actual prime-residue-field and quotient-dimension versions are
   also proved. This works for reducible or nonreduced finite-type
   algebras, without asserting an ambient stalk-dimension increment.

   **Affine dimension-function checkpoint (A11ag / SP48):**
   `AffineDimensionFunction.lean` combines strict prime-residue degree drop,
   SP47 and the reused `specPointOrderIso` into the existing dimension-function
   structure on literal \(\operatorname{Spec}A\). Both laws are proved,
   and its value equals actual finite point-closure dimension.
   `AffineSchemeDimensionFunction.lean` extracts the finite-type sections
   algebra from an actual affine structural morphism
   \(p:X\to\operatorname{Spec}k\) and transports through `X.isoSpec`
   using existing closed-immersion restriction. Its function is literally
   integer point height. No separate sections algebra or grading-law input
   is required. The actual support-degree and fundamental-cycle membership
   tests identify geometric dimension, also on reducible or nonreduced
   ambient affine schemes and without a dimension-at-most-one bound.

   **Structural residue-field checkpoint (A11ah / SP49):**
   `StructuralResidueField.lean` derives the base action on the actual
   scheme residue field by pulling back and evaluating global constants.
   The action is independently defined and locally installed. Naturality
   proves that actual residue maps are base-algebra maps; actual open
   immersions give base-algebra equivalences. `AffineResidueField.lean`
   constructs the stalk-induced comparison with `Ideal.ResidueField`,
   proves its equality on every \(A\)-constant, and upgrades it to an
   algebra equivalence over any commutative base. Over a field,
   `AffineResidueFieldDimension.lean` preserves full transcendence degree,
   proves its finiteness for a finite-type ambient algebra, and identifies
   the existing literal-spectrum dimension function with actual scheme
   residue degree. It also proves full-cardinal invariance under arbitrary
   open immersions. No finite-type hypothesis on residue fields is asserted.

   **Structural affine-value checkpoint (A11ai / SP50):**
   `AffineSchemeResidueDegree.lean` proves finite structural residue degree
   on every actual affine \(X\) with locally finite-type \(p\) and
   identifies it with the existing `ofAffineLocallyOfFiniteType` value.
   The proof extracts the actual finite-type sections algebra, retains
   the spectrum-morphism equality and checks the composite with
   `X.isoSpec.hom` is the original \(p\). Thus SP49 transports the
   actual structural action, not just the field carrier. The existing
   `point_height_iso` is exposed unchanged and reused. No second dimension
   function or preinstalled sections algebra is introduced. The affine
   values agree under every open immersion between affine schemes over
   this field, using the pulled-back source structural map.

   **Chartwise value checkpoint (A11aj / SP51):**
   `ChartResidueDegree.lean` proves finite structural residue degree at
   every point of an arbitrary locally finite-type \(k\)-scheme using
   one actual affine chart. Neither ambient affineness, quasi-compactness,
   a finite subcover nor a global dimension bound is required. For any
   affine open chart, its existing dimension value equals the actual
   structural residue degree at its ambient image. Two chart values
   therefore agree when their actual ambient images agree. The
   point-dependent scalar action is retained throughout; no global
   dimension-function object is introduced by these value theorems.

   **Global dimension-function checkpoint (A11ak / SP52):**
   `FieldDimensionFunction.lean` constructs the actual structural
   residue-degree function on every locally finite-type \(k\)-scheme.
   An affine neighbourhood of the specialized point contains the
   generizing point. Specialization reflection through the actual open
   embedding transfers strict order and the cover relation into that
   chart. SP51's value comparison and the existing affine laws
   prove global strictness and the immediate-specialization unit step.
   The function is nonnegative, equals the existing affine construction
   as a whole object, and has compatible values under arbitrary open
   immersions over the field. No affine, quasi-compact or integral
   ambient premise or supplied gluing package is used.

   **Global height/carrier checkpoint (A11al / SP53):**
   `FieldSupportDimension.lean` identifies the constructed function with
   actual point height and reduced point-closure dimension. Nonnegative
   strictness supplies the upper bound; one actual affine chart, finite
   affine height and the proved normalization supply the lower bound.
   Each point height and each integral closed carrier dimension is finite
   without a global bound, quasi-compactness or Noetherianity of \(X\).
   The existing support degree is its actual carrier dimension, and
   fundamental-cycle membership in natural degree \(n\) is equivalent
   to dimension \(n\) for nontrivial coefficients. Actual open immersions
   preserve point height in this locally finite-type field setting.

   **Integral codimension checkpoint (A11am / SP54):**
   `IntegralCodimension.lean` proves finite integral ambient dimension,
   point coheight and actual support codimension, and
   \(\operatorname{codim}_X W+\deg_{\delta_{X/k}}W=d\), where
   \(d=\delta_{X/k}(\eta_X)=\dim X\). It also proves the full
   extended equality \(\operatorname{codim}_X W+\dim W=\dim X\).
   Finite-coheight induction uses the existing unit-step law, not a
   supplied uniform-chain theorem. The degree-\(d-n\) submodule is
   exactly finite cycles with nonzero coefficients on actual
   codimension-\(n\) carriers. Subtraction is in the integers, without
   an assumed \(n\leq d\); the fundamental-cycle converse retains
   nontrivial coefficients. No new carrier or cycle module is introduced.

   **Principal-relation codimension checkpoint (A11an / SP55):**
   `PrincipalRelationCodimension.lean` identifies the existing relation
   data in degree \(d-(n+1)\) with the same codimension-\(n\) carriers
   and units in their actual function fields. The carrier, function and
   ambient divisor are preserved by definitional equality. These are
   relations on codimension-\(n+1\) cycles. The data equivalence has no
   Noetherian premise; the existing relation map retains it.
   In `PrincipalRelations.lean`, generic-degree relation data are empty
   for any integral scheme with any supplied dimension function, without
   requiring a field or finite type. The existing Noetherian relation
   span is zero in that degree and rational equivalence is equality.

   **Rational coefficient checkpoint (A11ao / SP56):**
   `CoefficientExtension.lean` constructs coefficientwise cast on the
   existing homogeneous cycles and identifies their rational module with
   the scalar extension of the integral module. The equivalence sends
   \(q\otimes c\) to \(q c_{\mathbb Q}\), without an integrality,
   Noetherian or finite-type premise. `RationalChow.lean` defines the
   rational span of the same actual principal generators and proves
   \[
    \mathbb Q\otimes_{\mathbb Z}\operatorname{CH}_m^\delta(X)
    \simeq\operatorname{CH}_m^\delta(X;\mathbb Q),\qquad
    q\otimes[c]\longmapsto[q c_{\mathbb Q}].
   \]
   The rational class map is surjective and has precisely that relation
   kernel. The integral-to-rational Chow map preserves representatives;
   generic-degree relations still vanish. The quotient retains the
   existing Noetherian premise. The generic scalar-extension quotient
   proof uses universal properties, not flatness or an injectivity
   assumption; Chow rationalization may kill torsion.

   **Rational operation checkpoint (A11ap / SP57):**
   The graded closed pushforward now has one semiring-parametric core;
   its original integer names are definitional specializations.
   `CoefficientPushforward.lean` proves coefficient-cast compatibility
   on actual ungraded and homogeneous cycles, and degree preservation
   for the actual isomorphism open restriction, without Noetherianity.
   `RationalChowPushforward.lean` reuses the proved integral
   principal-generator image theorem to preserve the rational relation
   span and descend to rational Chow. Its actual representative,
   identity/composition, integral-rationalization and tensor-comparison
   formulas retain the original degree-compatibility and Noetherian
   premises. The canonical restricted dimension function supplies the
   degree compatibility. `RationalChowIsomorphism.lean` identifies the
   scalar extension of the existing integral Chow isomorphism with that
   geometric rational pushforward, and identifies its inverse on actual
   rational cycle representatives with the existing open restriction.
   Neither a second graded-isomorphism construction nor cancellation of
   Chow rationalization is used.

   **Integral-open local comparison checkpoint (A11aq / SP58):**
   `FunctionFieldTransport.lean` now constructs the contravariant
   function-field equivalence for an actual open immersion of integral
   schemes, together with its actual stalk-specialization and local
   algebra-map compatibility. No Noetherian or compactness premise is
   needed, and the previous isomorphism APIs specialize this same map.
   `SchemeLocalOrder.lean` proves local stalk-dimension invariance and
   embeds divisor points for open immersions of arbitrary schemes. The
   image is exactly the target divisor points in the actual open image,
   not all target divisor points. On integral schemes, target local
   Noetherianity suffices for the actual signed-order comparison; source
   local Noetherianity is derived. The existing isomorphism order theorem
   is a specialization and the existing point-equivalence forward map
   agrees with the new embedding.

   **Open-support and principal-divisor checkpoint (A11ar / SP59):**
   `OpenSupport.lean` proves that reduced ambient closure and nonempty
   actual ideal-comap restriction are inverse on integral supports.
   The nonempty criterion uses the actual ambient generic point, and
   chain codimension is preserved. For any semiring, the existing
   restriction reads the coefficient of the corresponding reduced
   ambient closure. None of these support/cycle statements requires
   ambient integrality, Noetherianity or compactness; empty restricted
   generators remain zero. `PrincipalDivisorTransport.lean` now proves
   restriction of principal divisors for integral open immersions.
   Target local Noetherianity and quasi-compactness supply the source
   hypotheses through the actual open map, so finite-cycle assembly is
   justified on both sides. The old isomorphism restriction theorem is
   a specialization. Neither a new cycle module nor a closed-image
   operation on the open immersion is used.

   **Grading and closed-carrier square checkpoint (A11as / SP60):**
   `OpenGrading.lean` constructs literal dimension-function restriction
   along an open immersion, proving strictness and the immediate-step
   condition from the actual specialization order. Both support degree
   comparisons are proved, and existing open restriction preserves the
   existing homogeneous cycle modules over every semiring. Its graded
   linear map retains actual representatives and identity/composition.
   The old isomorphism homogeneity theorem specializes it; open and
   closed restrictions of the dimension function agree when both apply.
   `OpenClosedBaseChange.lean` proves the raw finite-cycle square for
   an actual integral closed carrier and its possibly empty ideal-comap
   inverse image. Its proof compares actual generators, not an assumed
   base-change operation. These constructions need no ambient integral,
   Noetherian or compactness hypothesis.

   **Ambient generators and relation preservation (A11at / SP61):**
   `PrincipalDivisorRestriction.lean` proves the nonempty ambient
   principal-divisor restriction formula with the actual support
   function-field pullback, and the zero formula for an empty restricted
   carrier. Only local Noetherianity and quasi-compactness of the carrier
   are assumed; ambient finiteness and integrality are unnecessary.
   `PrincipalRelationRestriction.lean` restricts nonempty relation data
   with the same actual carrier, pulled-back unit and degree `n + 1`.
   This data construction needs no Noetherian premise. With Noetherian
   target, source Noetherianity is derived; the genuine graded relation
   generator restricts to its nonempty counterpart or to zero. The
   resulting span inclusion and preservation of the existing rational-
   equivalence predicate are proved, not supplied as inputs.

   **Open Chow maps and coefficient compatibility (A11au / SP62):**
   `ChowOpenRestriction.lean` descends the existing actual graded map
   through SP61's proved relation inclusion. It retains actual cycle
   representatives, identity and contravariant composition, with
   source Noetherianity derived from the target. `CoefficientRestriction.lean`
   proves that integer-to-rational coefficient extension commutes with
   the same raw and graded maps, without finiteness hypotheses.
   `RationalChowOpenRestriction.lean` proves rational-span preservation
   from the actual generator branches and descends the rational map.
   Its representative, identity/composition, integral-to-rational and
   full tensor-comparison formulas are proved. No injectivity of
   `chowRationalize` is used, and the quotient maps retain target
   Noetherianity as an explicit hypothesis.

   **Open restriction surjectivity (A11av / SP63):**
   `OpenRestrictionSurjectivity.lean` lifts finite cycles through reduced
   ambient support closures. The actual ideal-comap identity proves a
   cycle-level right inverse; the support-degree identity makes the lift
   homogeneous. Raw and graded restriction are thus surjective over every
   semiring without finiteness hypotheses. The integral and rational Chow
   maps are surjective by choosing and lifting actual homogeneous cycle
   representatives, with only target Noetherianity assumed. The private
   closure lift is not a Chow map: preservation of rational equivalence
   by that lift is not supplied or used.

   **Next bounded obligation:** prove the actual closed-complement
   support/kernel/image comparison on finite and homogeneous cycles.
   Construct the reduced closed complement using the existing vanishing
   ideal of the complement of `Set.range j.base`. Compare closed-image
   supports with ambient generic points outside this range, and use the
   existing open coefficient formula to identify the restriction kernel.
   The graded comparison uses the actual restricted dimension functions.
   Quotient localization exactness additionally needs a principal-relation
   lifting argument and remains a separate proof.
   The target's actual
   rational Chow groups and their intersection/Betti structure still
   require a geometric identification.
   A pure-dimensional or componentwise extension is needed
   for reducible targets; smoothness alone does not make all connected
   components have the same dimension. The current integral quotient's
   Noetherian premise is retained; the general scalar-extension comparison
   is now proved independently of the earlier split-case adapter.
   General proper pushforward still needs its norm
   compatibility; localization exactness remains to be proved, and general flat/Gysin operations need
   their own principal-relation comparisons and quotient descent.
   Absolute
   relations may use larger-dimensional supports outside the relative
   product, so no injectivity on Chow follows from the closed inclusion.
   Establish flat/Gysin comparison and properness
   on the selected domain before promoting `graphCycleLinearMap` to a
   Chow algebra map. No claim that \(r\) is étale follows from étale \(p\).
   The supportwise outer pushforward is proved; an ambient projection map
   on all cycles is not supplied merely by separatedness.

3. **For the optional projector route, connect the auxiliary geometry to
   the prescribed Hodge target.** Fix
   \((X,p,\alpha)\) independently of the cover. Graph correspondences on
   \(\bar Y\) do not automatically act on
   \(\mathbb Q(-p)\oplus H^{2p}(X,\mathbb Q)\). Name the actual geometric
   correspondence or morphism connecting them, with its degree, variance,
   properness, and multiplication compatibilities. Construct the genuine
   target Chow/Betti model and its detection map, then the residual map and
   chosen projector in that target. **Acceptance:** prove
   \(\theta(a_H)=\alpha\) and
   \(\rho(\Pi)\Theta=\Theta P_{a_H}\) from the geometric construction.
   For the full chosen-projector conclusion, prove residual surjectivity
   for the current cancellation argument, or prove the full action equality
   directly. No recipe may begin by choosing a cycle representing
   \(\alpha\). Writing a non-circular candidate for this step is an early
   design gate, not something postponed until the graph infrastructure is
   finished.

4. **Establish coverage and discharge the remaining inputs.** Show that
   the construction works for every prescribed class in the claimed
   geometric family; identify which hypotheses are proved and which remain
   source inputs. The universal Hodge conclusion requires all genuine
   \(X,p\), not just a supplied abstract indexing family. Keep the
   additional Galois replacement theorem separate if the stronger reverse
   coverage equivalence is also sought. **Acceptance:** instantiate the
   existing endpoint using constructed data, with no hypothesis that is
   merely the desired class-generation or realization conclusion renamed.

After B4i's finite-normalization construction, B4j constructs the finite
etale tensor source and actual evaluations, proves generic surjectivity
from normal-closure generation, and identifies the corresponding generic
kernel quotient with `N`. B4k constructs the canonical localization/base-
change comparison `K⊗_B P_B ≃ P_K` and proves equality of evaluator
homomorphism composites. B4l constructs the selected generic factor and
its canonical idempotent under separability. B4m proves the actual
integral section and selector, the evaluation-preserving quotient
comparison with `IntCl_B(N)`, and its whole-ring finite-etale conclusion.
The focused suite verifies the actual scheme-chart ring specialization
without Noetherianity. B4n implements the named actual affine normalized
cover, its finite-etale structural maps and marked refinement, with exact
factorization on the chart and over `X`; the checkpoint is validated.
B4o proves same-ambient localization, principal-open restriction and
both actual structural/refinement squares on nested affine charts.
Its generic identity/composition laws are proved. Next assemble actual
overlap/coherence and cocycle data, gluing and the compatible global
Galois action. The trace-section route bypasses
whole-source integral-closedness and needs no Noetherian-base premise.
The earlier affine-cover interfaces retain their explicit base normality,
Noetherianity and upstairs-normal-stalk inputs; the global Galois
refinement remains subsequent. Finiteness and full-visible separation
are already proved without a separately supplied second affine algebra.
The existing
fixed-field, selector and trace consumers now use extension separability;
core-freeness and its full-visible/inertia/extension consumers need none.
Deriving normal stalks from smooth geometry, the global finite etale
Galois refinement and gluing remain separate.
Finiteness and etaleness of the actual
inverse-image section algebra now follow from the scheme morphism; the
normalization identification uses the existing upstairs function field
and commutes over the original base. A genuinely nonempty-boundary route remains an
alternative requiring its own quotient regularity or all-section landing.
The projective-bundle recipe, its PB0 chart, and the
elliptic curve/chart/point construction are optional deferred examples;
their detailed analyses are preserved above.
L1 is the next bounded
Lean checkpoint for the ongoing localization stream, not a universal
prerequisite for every geometric route. Actual integral/rational Chow
quotients and their surjective open maps are constructed; the general
graph-to-Chow algebra, target action and class coverage remain the distinct
obligations recorded above.
