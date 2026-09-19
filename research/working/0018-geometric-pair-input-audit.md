# Geometric input audit and regular-pair controls

Date: 2026-09-18. Checkpoint: SP69. This is a research audit, not a new
manuscript theorem or a completed Hodge construction. The production
regular-pair criterion from SP68 is unchanged.

## 1. What the current cover package supplies

`HodgeConjecture/Boundary/Normalization/InertiaDiagram.lean` defines
`NormalizedCover` using a marked finite normal closure, finite intermediate
and normal-closure normalization models, and an open immersion of the
visible scheme. It does not require that open immersion to be surjective
or that the normalization be unramified along the deleted locus.

The active library audit found consumers of a supplied `NormalizedCover`,
but no construction of one from a specific smooth projective variety and
cover. The split Chow/Betti examples are actual constructions in a separate
part of the library; they do not instantiate this normalization package.
Consequently, there is not yet application-specific boundary geometry
from which the regular pairs can be extracted.

The existing theorems provide two useful ingredients, not the missing pair:

- `fixedLocusIdeal_ne_bot` supplies a nonzero element of the fixed ideal.
- `intermediateFixingSubgroup_normalCore_eq_bot`, over a perfect base
  field, makes the action on conjugate sheets faithful.

Neither ensures that a moving-boundary element acts injectively modulo a
chosen fixed element. Choosing that first element arbitrarily is itself
unsafe for this purpose, as the formal controls below show.

## 2. A deleted ramification divisor survives all the weak inputs

This is an explicit mathematical model, not a Lean construction of a
`NormalizedCover` in this checkpoint. Let `k` have characteristic zero and
take

\[
 B=k[x],\quad K=k(x),\quad L=N=k(t),\quad x=t^2,\quad T=k[t].
\]

The finite normal extension has involution `t -> -t`. Its normalization is
`T`: this ring is finite over `B`, integrally closed, and has fraction field
`N`. Mark the open `U=D(t)` in `Spec T`.

The visible map is étale: its presentation is
`B[t,1/t]/(t^2-x)`, with derivative `2t` invertible. This uses the
[standard étale definition, Stacks 00UB](https://stacks.math.columbia.edu/tag/00UB)
and [standard étale implies étale, Stacks 00UC](https://stacks.math.columbia.edu/tag/00UC).
It is finite étale over `D(x)`, not a finite cover of all of `Spec B`.

For the nontrivial subgroup `I`, every difference `h(-t)-h(t)` is divisible
by `t`, and the difference for `h=t` is `-2t`. Hence `J_fix(I)=(t)`.
The deleted set `V(t)` is invariant under the involution; both moved sheets
have boundary ideal `(t)`. Therefore

\[
 J_{\mathrm{fix}}(I)=J_{\mathrm{mov}}(I)
   =J_{\mathrm{fm}}(I)=(t).
\]

The height-one prime `(t)` contains this ideal. Thus separation fails,
and the already proved SP67 pole theorem obstructs uniform trace landing.
No regular pair in this combined ideal can satisfy the SP68 criterion.
For `k=C`, the same local model is the affine chart of the squaring map
`P^1 -> P^1`, whose restriction to `G_m` is étale. A smooth projective
ambient variety does not, by itself, remove this boundary issue.

This is a counterexample to an implication from the *current weak cover
inputs*, not a counterexample to the Hodge conjecture or to SP68.

## 3. Formal algebra controls: the choice of first element matters

`research/RegularPairGeometryControls.lean` is a standalone research file,
outside the production imports and centralized production declaration
inventory. Its checks use the existing quotient and ideal
carriers, not a new geometric-input package.

In the nested polynomial ring `Q[y][x]`, put `A=(x)` and `M=(y)`.
The choice `f=x`, `g=y` works: modulo `x` the ring is `Q[y]`, where
multiplication by `y` is injective. The existing generic SP68 theorem
then excludes height-one primes containing `A+M`. A separate check proves
`A+M` is proper, so this is not a unit-ideal example.

But `f=xy` is also a nonzero element of `A`. For this first element,
**no** `g in M` is regular modulo `f`: the nonzero residue class of `x`
is annihilated by every multiple of `y`. Thus nonzero fixed-element
existence cannot be combined with an arbitrary subsequent choice of a
moving element.

The general algebraic obstruction is: in a domain, if `a != 0` and `b`
is not a unit, then every `g in (b)` is a zero divisor on `T/(ab)`.
Indeed `g*a in (ab)`, while `a in (ab)` would force `b` to be a unit by
cancellation. These are algebraic controls; `A` and `M` have not been
identified with the actual fixed and moving ideals of a constructed cover.

Validation: `lake env lean research/RegularPairGeometryControls.lean`
passes without warnings. All eight named diagnostic theorems pass the
enforced axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`).
`lake build` also passes (3161 jobs), with only the pre-existing expected
`Challenge.lean` placeholder warnings. The production declaration
inventory, manuscript, and PDF are unchanged; the inventory audit and PDF
build were not rerun for this research checkpoint. No production theorem
or global hypothesis changes are required by this audit.

## 4. Exact obstruction for a specified first element

For a Noetherian ring `T`, a specified `f`, and an ideal `M`, the
mathematical existence test is

\[
 \exists g\in M\text{ regular on }T/(f)
 \quad\Longleftrightarrow\quad
 \forall\mathfrak p\in\operatorname{Ass}_T(T/(f)),\quad
 M\nsubseteq\mathfrak p.
\]

This follows from finiteness of associated primes for the finite module
`T/(f)`, the description of zero divisors as their union
([Stacks 10.63.5 and 10.63.9](https://stacks.math.columbia.edu/tag/00L9)),
and [finite prime avoidance, Stacks 00DS](https://stacks.math.columbia.edu/tag/00DS).
The zero quotient is allowed; then regularity is vacuous.

The pinned Mathlib has `associatedPrimes.finite`,
`biUnion_associatedPrimes_eq_compl_regular`, and
`Ideal.subset_union_prime_finite`. This is an available reduction, not a
newly formalized existence theorem or a proof of geometric avoidance.
For the boundary route, the missing content is how the actual moving
ideal avoids these primes for a suitably chosen actual fixed element.

## 5. Choose the geometric construction before adding more criteria

Two different next constructions remain possible:

1. **Finite étale cover over the whole smooth projective base.** Build
   its affine normalization data with the entire intermediate model
   visible. In the full-visible situation every conjugate boundary ideal
   is the unit ideal. Core-freeness makes a nontrivial subgroup move some
   sheet, so `J_mov(I)=T`; a nonzero fixed element and `g=1` give a pair.
   This is a mathematical positive subclass, not yet implemented here.
   The class-generation problem under the Chow--Betti map remains separate.
2. **A genuinely nonempty boundary compactification.** Specify the actual
   cover and compactification, compute their fixed and moving ideals, and
   identify an independent condition excluding the ramified-divisor model
   above. Étaleness on the visible open, normality, and finite denominator
   clearing alone cannot supply that condition.

Neither choice changes the main smooth-projective Hodge target. The
full-visible condition must not be silently added to the general route.
The next design choice has been requested from the user. Until that choice
is settled, do not replace the construction with another assumed regular
pair, associated-prime avoidance assertion, or uniform landing package.

## 6. SP70 follow-up: finite etale/full-visible route selected

The user selected the first option: begin with finite etale covers over
the whole smooth projective base, and reconsider nonempty-boundary
geometry only if needed. The SP69 audit above is retained as its dated
record; its then-open design choice is now settled.

The bounded affine checkpoint constructs the existing `NormalizedCover`
from actual finite normal affine algebras with compatible marked fraction
fields and supplied `NormalClosureData`. The canonical normalization map
is identified with an equivalence, carrying finiteness and etaleness to
the existing normalization models. The constructor
`normalizedCoverOfFiniteNormalAffineModels` in `FiniteAffineCover.lean`
requires finite normal rings, not etaleness; the separate
`normalizedCoordinateRing_etale` preserves etaleness when given.
The whole intermediate model is
visible. For any surjective visible open, all conjugate boundaries are
empty; over perfect `K`, the core-free action makes
`J_mov(I)=J_fm(I)=top` for each nontrivial subgroup and proves separation
directly via `conjugateBoundarySeparation_of_surjective` in
`FullVisibleBoundary.lean`. No regular-pair detour or additional ideal is
needed.

Full visibility and boundary separation alone do not imply etaleness or
unramifiedness: the separate etale hypothesis is still needed for the
intended finite etale application.

The full build passes (3163 jobs; only the two expected unchanged
Challenge placeholder warnings). Twenty focused regressions and enforced
standard-axiom audits for all seventeen new declarations pass without
warnings. The fresh unchanged dependency audit passes its six endpoint
contracts and two support reports. The central inventory has 798 checks,
565 examples and 690 reports after appending seventeen checks and reports;
the unchanged historical prefix was not rerun in full.

This does not construct a global smooth-projective finite etale cover or
its Galois closure, deduce
normality from etaleness in general, or glue the affine data. Those
geometric inputs and the separate Chow--Betti generation problem remain
visible in the current gap map. The single manuscript has matching
affine-identification and full-visible-separation propositions. Its
71-page PDF build, warning scan, visual checks and independent Lean--TeX
review pass.

## 7. SP71 follow-up: actual finite-morphism affine charts

The affine input is now derived from a supplied finite scheme morphism
`p:Y -> X` and affine open `U`: use the whole inverse image and the
existing section rings `B_U=Gamma(X,U)`, `A_U=Gamma(Y,p^-1 U)`.
`FiniteAffineChart.lean` proves `A_U` finite over `B_U`, and etale when
the morphism is etale. This algebra layer needs neither integrality,
nonemptiness nor normality. `AffineEtaleAlgebra.lean` supplies the general
scheme-smooth/etale to affine-algebra bridge.

For integral `Y` and nonempty inverse image, normality of the actual
stalks on that open gives normality of `A_U` by `AffineNormality.lean`.
The existing `Y.functionField` is its fraction field. The resulting
`finiteAffinePreimageNormalizationIso` identifies the actual open
subscheme with the normalization; its structural equality is proved over
the original `X`, and the normalization is finite and, when `p` is etale,
etale. No ring, field or cover package is replaced.

The full build passes (3174 jobs; only the two expected unchanged
Challenge placeholder warnings). Eighteen focused regressions and
enforced standard-axiom audits for all eleven new declarations pass
without warnings. The SP70 suite was freshly rerun and passes its twenty
regressions and seventeen audits; the fresh unchanged dependency audit
passes six endpoint contracts and two support reports. The central
inventory now has 809 checks, 565 examples and 701 reports after appending
eleven checks and reports; its historical prefix is unchanged and was not
rerun in full.

Normal stalks have not been derived from the
intended smooth geometry; a global finite etale Galois refinement,
marked generic extension/normal-closure data, chart gluing and the
separate Chow--Betti class-generation problem remain. Next construct
the canonical `K(X) -> K(Y)` for a dominant finite morphism of integral
schemes and prove finite-dimensionality from the actual section algebra, to supply the
generic extension layer; deriving normal stalks from smoothness remains
a larger foundational task. The manuscript
states the chart result with its exact hypotheses. The earlier SP69 and
SP70 audit records above are retained unchanged. The 72-page PDF build,
warning scan, visual checks and independent Lean--TeX review pass.

## 8. SP72 follow-up: the actual finite generic extension

`Cycles/FunctionFieldMap.lean` constructs the actual generic-stalk map
`kappa_p:K(X) -> K(Y)` for a dominant morphism of integral schemes.
Nonempty inverse images use only dominance; preservation of the generic
point uses irreducibility. The field map is injective, commutes with
section germs on every nonempty base open, satisfies identity and
contravariant composition, and agrees with the existing open-immersion
isomorphism. No chosen fraction-field carrier replaces either scheme's
actual function field.

`Boundary/Normalization/FiniteFunctionField.lean` turns the germ square
into the actual section scalar tower. For finite `p`, the finite whole
inverse-image affine section algebra localizes to prove finite-dimensionality
for this exact field map. The global endpoint chooses its nonempty affine
chart internally. Normality, etaleness, Noetherianity and a separately
supplied extension are not required.

The 72-page PDF build, warning scan, visual checks and independent
core/manuscript review pass. The full build passes (3176 jobs; only the
two expected unchanged Challenge placeholder warnings). Eighteen focused
regressions and eleven enforced standard-axiom audits pass without
warnings. The fresh SP71 rerun passes eighteen regressions and eleven
audits; the fresh unchanged dependency audit passes six endpoint
contracts and two support reports. The central inventory now has 820
checks, 565 examples and 712 reports, with eleven checks and reports
appended. Its historical prefix is unchanged and was not rerun in full.

Next construct marked normal-closure field data
from this actual finite extension and establish separability for the
Galois conclusion. Finiteness alone is not this separability input; the
scheme-etale route and characteristic zero/perfectness from the intended
complex scalar structure have not yet been connected to it.
The inspected `FormallyUnramified` localization/composition route is the
next priority, not a proved result here; separability of this extension
does not supply downstream perfectness of the base field.
Actual global Galois refinement, normal stalks from smoothness, gluing
and Chow--Betti generation remain separate. The manuscript uses
`\kappa_p`, the same generic germs and the same scalar square; no new
input package or source axiom is introduced. All earlier audit text is
preserved unchanged.

## 9. SP73 follow-up: separability of the actual generic extension

`Boundary/Normalization/SeparableFunctionField.lean` implements the
localization route for the same actual `kappa_p:K(X) -> K(Y)`. A dominant
affine formally unramified morphism of integral schemes gives formal
unramifiedness of this field algebra. The affine-chart result accepts a
nonempty affine base open; the global result chooses that chart internally.
This layer does not need a finite morphism.

For a finite dominant formally unramified morphism, the SP72
finite-dimensionality theorem supplies essential finite type, and the
existing Mathlib field theorem proves separability. Finite etale
morphisms satisfy the formal-unramifiedness hypothesis automatically.
No normality, perfectness, characteristic-zero or Noetherian hypothesis
is added. No replacement map, field or cover package is introduced.

The full build passes (3177 jobs; only the two expected unchanged
Challenge placeholder warnings). Sixteen focused regressions and three
enforced standard-axiom audits pass. The fresh SP72 rerun passes eighteen
regressions and eleven audits; the fresh unchanged dependency audit
passes six endpoint contracts and two support reports. The central
inventory now has 823 checks, 565 examples and 715 reports after three
checks and reports are appended; its historical prefix is unchanged and
was not rerun in full. The 73-page PDF build, warning scan and visual
checks pass.

Next construct marked normal-closure field data
from this actual finite separable extension. Existing downstream
`PerfectField K` consumers remain undischarged: separability of this
extension does not prove perfectness of the base field. Actual global
Galois refinement, normal stalks from smooth geometry, gluing and
Chow--Betti generation remain separate. All preceding audit text is
preserved unchanged.

## 10. SP74 follow-up: construct the marked finite normal closure

`NormalClosureConstruction.lean` constructs the existing
`NormalClosureData K L N` for every finite field extension `L/K`, using
`N=IntermediateField.normalClosure K L (AlgebraicClosure L)`. The marked
embedding retains the canonical inclusion of `L` in its algebraic
closure. The constructor does not require separability or perfectness.
For any supplied marked normal closure, separability of `L/K` gives
separability and Galoisness of `N/K`, without a perfect-base-field input.

`FunctionFieldNormalClosure.lean` applies this to the actual generic-stalk
extension of a finite dominant morphism of integral schemes. Its marking
formula is the original upstairs-field inclusion. Scheme formal
unramifiedness supplies separability through SP73, hence Galoisness of
the constructed normal closure; finite etale morphisms qualify.
The same package and Mathlib intermediate-field carrier are reused.

The 74-page PDF build, warning scan, visual checks and independent
core/scheme/manuscript review pass. The full build passes (3179 jobs;
only the two expected unchanged Challenge placeholder warnings).
Twenty-two focused regressions and seven enforced standard-axiom audits
pass. The fresh SP73 rerun passes sixteen regressions and three audits;
the fresh unchanged dependency audit passes six endpoint contracts and
two support reports. The central inventory now has 830 checks, 565
examples and 722 reports after seven checks and reports are appended;
its historical prefix is unchanged and was not rerun in full.

Next connect this extension-specific Galois
result to existing fixed-field, core-free and selector consumers,
replacing avoidable perfectness assumptions. Their signatures have
not been refactored in SP74, and perfectness of the base field is not
proved. The next-proof audit suggests extension separability for the
fixed-field and selector/tensor comparisons, but no separability premise
for core-freeness itself; removal in that proof and its full-visible
boundary consumers is not yet implemented. Actual scheme-level Galois
refinement, normal stalks from
smoothness, normalization gluing and Chow--Betti generation remain
separate. The manuscript uses the existing `\mathcal N` with the
canonical marking; its Stacks citations are attribution, not source
axioms. All preceding audit text is preserved unchanged.

## 11. SP75 follow-up: local-separability consumer generalization

Fourteen fixed-field, invariant-ring, selector/tensor and trace/pole
declarations now use explicit `Algebra.IsSeparable K L`, rather than a
perfect base field. Core-freeness needs neither separability nor
perfectness; eleven full-visible, inertia, sheet and projector consumers
also lose their perfect-field binders without replacement. All other
geometric hypotheses are retained.

The existing `NormalClosureData.isSeparable` and
`.isGalois_of_isSeparable` move to `NormalClosure.lean` under their
unchanged names. The existing `.isGalois [PerfectField K]` remains as the
sole perfect-field compatibility wrapper, delegating through separability
of the finite marked extension. No library declaration, package, field carrier,
map, ideal, projector or source axiom is added: there are 26 signature
generalizations, two moved helpers and one wrapper-proof change.

Validation: the new consumer suite passes 24 examples and 29 enforced
standard-three axiom audits; the trace and pole suites pass 14/11 and
12/9. Fresh SP74 and finite-affine-cover suites pass 22/7 and 20/17.
The central inventory has 859 checks, 565 examples and 751 reports
after appending 29 checks and reports; its historical prefix is
byte-identical and was not rerun in full. The 74-page PDF (785575 bytes)
passes its build, warning/box/reference scan, visual checks of pages
9--13, 57 and 66--67, and independent Lean--TeX review. The full build
passes (3179 jobs; only the two existing Challenge placeholder warnings).
The fresh unchanged dependency audit passes six endpoint contracts and
two support reports.

Next derive finiteness of the actual
`integralClosure B N` from the constructed finite separable normal
closure over normal Noetherian affine `B`, instead of supplying a second
finite normal algebra `S`. Mathlib's inspected `IsIntegralClosure.finite`
needs no dimension-one or Dedekind hypothesis; its specialization is
not yet implemented. Normality of `B` remains explicit. Etaleness of
the resulting `N`-model, overlap compatibility, gluing and the global
finite etale Galois refinement remain subsequent geometric tasks.
Normal stalks from smoothness and Chow--Betti generation remain separate.
All earlier audit text is preserved unchanged.

## 12. SP76 follow-up: finite normal-closure normalization and actual affine cover

`FiniteNormalClosure.lean` proves finiteness of the existing integral
closure over normal Noetherian `B` in a finite separable extension of its
fraction field. Specializing to the marked normal closure constructs
its finite model from `D.finiteNormal` and `D.isSeparable`. No separately
supplied second finite normal algebra `S` is needed; the one-intermediate-
model constructor uses the existing normalization map and derives
full-visible boundary separation.

For a finite dominant formally unramified morphism `p:Y -> X` of integral
schemes and nonempty affine `U`, the actual generic extension constructs
the marked normal closure and its finite normalization over `Γ(X,U)`.
With normality/Noetherianity of that base ring and normal stalks on the
whole inverse image explicit, `finiteAffinePreimageNormalizedCover`
constructs the existing cover with actual visible scheme `(p⁻¹U).toScheme`
and the existing normalization-isomorphism map. Its separation theorem
uses full visibility. No independent `S` or marked closure is supplied;
no new carrier, cover package or source axiom is introduced.

Finite etale morphisms satisfy the formal-unramifiedness premise. The
finiteness API has no perfectness, dimension-one or Dedekind assumption;
its exact standard counterpart is Stacks Lemma 10.161.8, Tag 032L.
Validation: the full build passes (3180 jobs; only the two existing
Challenge placeholder warnings). The new suite passes 23 examples and
seven enforced standard-three axiom audits; fresh consumer, affine-chart
and normal-closure suites pass 24/29, 18/11 and 22/7. The central inventory
has 866 checks, 565 examples and 758 reports after appending seven checks
and reports; its historical prefix is byte-identical and was not rerun
in full. The 74-page PDF (788608 bytes) passes its build, warning/box/
reference scan and visual checks of pages 8--10, 57, 66--67 and 73--74;
independent code and Lean--TeX reviews pass. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.

Next identify this specific finite `N`-normalization
as a direct factor of a finite tensor construction from the actual finite
etale intermediate algebra. The comparison and whole-chart etaleness are
not yet proved; generic etaleness, localization to `N`, finiteness and
full-visible separation do not imply the whole-chart result. Overlap
compatibility and gluing follow as separate tasks. The actual global finite etale
Galois refinement, normal stalks from smooth geometry and Chow--Betti
generation remain separate. All earlier audit text is preserved unchanged.

## 13. SP77 follow-up: finite tensor source and marked evaluations

The finite tensor construction now has actual integral and field maps.
`FiniteTensorProduct.lean` proves the existing finite-index tensor
product finite when its factors are finite, and etale when its factors
are etale; the empty index case is included. No new tensor carrier is used.

For `Σ=Hom_K(L,N)`, `NormalClosureTensor.lean` evaluates
`P_K=⊗_{Σ,K}L` in the existing marked normal closure by multiplying
the corresponding conjugate images. The range is an intermediate field
and contains every conjugate, so the normal-closure property proves
surjectivity. The actual kernel `m` is maximal and the quotient
`P_K/m` is canonically equivalent to `N`. This uses neither separability
nor an independently supplied surjectivity premise.

`NormalizationTensor.lean` restricts those same embeddings to the
existing integral closures, obtaining
`ev_B:P_B=⊗_{Σ,B}IntCl_B(L) -> IntCl_B(N)`. Its factor formula is the
existing `normalizationMap`; inclusion into `N` agrees on integral pure
tensors with the field evaluation. An actual finite normal intermediate
algebra `A` with fraction field `L` makes `P_B` finite. If `A/B` is
etale, `P_B/B` is etale by transport along the existing normalization
equivalence and the finite tensor theorem. The field marking and all
scalar compatibility are retained, without new source axioms or input
packages. The source-property theorems omit four unused base/target scalar
assumptions while evaluation retains its needed scalar towers. Stacks
Lemma 10.143.3, Tag 00U2, parts (2) and (3), supplies the checked standard
source for etale composition/base change only; it does not discharge the
integral factor comparison.

Validation: all 17 new APIs compile. The central inventory is 883 checks,
565 examples and 775 reports after appending 17 checks and reports; its
historical prefix is byte-identical and was not rerun in full. The 76-page
PDF (805454 bytes) passes its build and clean warning/box/reference scan;
visual checks of pages 9, 10, 58, 68, 69, 75 and 76 pass, as do independent
code and Lean--TeX reviews covering all 17 names. The full build passes
(3187 jobs; only the two existing Challenge placeholder warnings).
`NormalClosureTensorVerification.lean` passes 28 examples and 17 enforced
standard-three axiom audits without warnings. Fresh SP76 and SP74 reruns
pass 23/7 and 22/7, respectively: 73 examples and 31 audits in these three
suites. The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports.

Next construct the canonical tensor localization/base-change comparison
`K⊗_B P_B ≃ P_K` and equality of evaluator homomorphism composites; the
pure-tensor equality is not a substitute for that comparison. Then, under
separability, realize the generic maximal quotient as a direct factor/
idempotent; this splitting is not yet formalized. Subsequently extend/
select the integral factor and prove its image normal and equal to
`IntCl_B(N)`. The generic maximal-kernel quotient does not itself provide
either direct-factor identification. Whole-chart target etaleness,
overlap compatibility, gluing and the global finite etale Galois
refinement remain subsequent. Normal stalks from smooth geometry and
Chow--Betti generation remain separate. All earlier audit text is
preserved unchanged.

## 14. SP78 follow-up: canonical tensor base change and the evaluator square

The generic tensor base-change equivalence and factorwise algebra
congruence are constructed on the existing tensor carriers in
`PiTensorBaseChange.lean`, with exact factor and pure-tensor formulas.
`NormalizationBaseChange.lean` identifies `K⊗_B IntCl_B(L)` with `L`
by fraction-field localization and algebraicity. Its one-factor theorem
needs compatible scalar towers but no normality, Noetherianity,
separability or finite degree.

Composing these comparisons gives `β_Σ:K⊗_B P_B ≃_K P_K` for the
existing marked closure. The full identity
`ev_K∘β_Σ=β_N∘(1_K⊗ev_B)` is equality of algebra homomorphisms using
the existing evaluations and the same one-factor comparison for `N`.
It strengthens SP77's pure-tensor identity without supplying a commuting
square or replacing the marked field. The three common evaluation
helpers are relocated unchanged to `FiniteTensorProduct.lean`, with
their public names preserved. No new source axiom or input package is
introduced. The checked Stacks source is Lemma 10.36.11, Tag 0307, for
localization of integral closure, not for factor splitting or etaleness.

There are thirteen new APIs (seven generic tensor and six normalization
declarations), separate from the three relocated helpers. The central
inventory is 896 checks, 565 examples and 788 reports after appending
thirteen checks and reports; its historical prefix is byte-identical and
was not rerun in full. The 76-page PDF (812185 bytes) passes its build and
clean warning/box/reference scan; visual checks of pages 10, 11, 58, 68,
69, 75 and 76 pass. Both new leaves compile without warnings.
`NormalizationBaseChangeVerification.lean` passes 25 examples and 13
enforced standard-three axiom audits, including three actual function-field
cases. The full build passes (3189 jobs; only the two existing Challenge
placeholder warnings). Fresh SP77, SP76 and SP74 reruns pass 28/17, 23/7
and 22/7, respectively: 98 examples and 44 enforced axiom audits across
the four suites. The fresh unchanged dependency audit passes six primary
endpoint contracts and two support reports.

The next
bounded proof is generic direct-factor/idempotent splitting under
separability. Then extend/select the integral factor, prove its image
normal and equal to `IntCl_B(N)`, and derive whole-chart etaleness.
Neither generic splitting nor the integral identification is formalized
by the present comparison. Overlaps, gluing and global Galois refinement
remain later steps; normal stalks from smooth geometry and Chow--Betti
generation remain separate. All earlier audit text is preserved unchanged.

## 15. SP79 follow-up: the selected generic evaluation factor

The existing field tensor now has a selected product factor for the
actual marked evaluator. `NormalClosureFactor.lean` proves `P_K` finite
without separability; extension separability makes `P_K` etale and hence
reduced Artinian. `ReducedArtinianFactor.lean` splits the actual
maximal-ideal product at `m=ker(ev_K)` and uses the already constructed
quotient equivalence to identify that factor with `N`. It gives
`Φ_m:P_K ≃_K N × Q_m`, where `Q_m=Π_{I ≠ m} P_K/I`, and proves
`pr₁∘Φ_m=ev_K` as equality of algebra homomorphisms.

The selected element `e_m=Φ_m⁻¹(1,0)` is idempotent, has value one
under `ev_K`, annihilates exactly the evaluation kernel, and satisfies
`m=(1-e_m)`. Value one and kernel annihilation characterize it uniquely,
without assuming idempotence separately. No choice of field marking,
surjectivity or splitting is inserted as a new input. These are
statements about the existing algebra, not a unital section `N -> P_K`
or a new Chow projector. The source classification is Stacks Lemma
10.143.4, Tag 00U3, verified only for etale algebras over a field; the
specific factor and evaluator compatibility are direct Lean proofs.

The sixteen APIs comprise nine generic reduced-Artinian declarations
and seven marked normal-closure declarations, all registered. Validation
completed on 2026-09-19 after the checkpoint began on 2026-09-18. Both
leaves compile without warnings; the full build passes 3195 jobs with
only the two existing Challenge warnings. The focused suite and four
fresh neighbor suites pass 123 examples and 60 enforced standard-three
axiom audits. The fresh unchanged dependency audit passes six primary
endpoint contracts and two support reports. The central inventory is
912 checks, 565 examples and
804 reports; its historical prefix is unchanged and was not rerun in
full. The 78-page PDF (819834 bytes) passes build, warning scan and
seven-page visual review; independent mathematical/Lean--TeX review
passes. The SP79 parity-queue entry records detailed validation.

The next bounded obligation is to prove the required integral-closedness
of `P_B` inside `P_K`, descend this canonical generic idempotent, and
identify the selected image with `IntCl_B(N)`. Its idempotent equation
alone does not establish descent, and `P_B` need not be a domain.
The generic product decomposition does not discharge
that integral comparison or whole-chart etaleness. Overlap compatibility,
gluing, the global finite etale Galois refinement and normal stalks from
smooth geometry remain separate. Chow--Betti generation is unchanged.
All earlier audit text is preserved unchanged.

## 16. SP80 follow-up: the actual integral normalization factor

The checkpoint is proved and validated. The previous proposed
whole-source integral-closedness route is bypassed by constructing an
integral selector directly. It is not asserted that all of `P_B` is
normal or integrally closed inside `P_K`.

For normal `B` with fraction field `K`, finite `N/K`, and
`T=IntCl_B(N)`, `UnramifiedIntegralFactor.lean` contracts the existing
unramified separability section by the integral trace. For an actual
`f:S -> T`, with `S/B` formally unramified and essentially of finite
type, this gives a `B`-linear map `r:T -> S` respecting the source
action: `r(f(s)*t)=s*r(t)`. If the image of `S` spans `N` over `K`,
the central separability-tensor identity from `SeparabilityTrace.lean`
gives `f∘r=id`. The resulting `E=r(1)` is idempotent, evaluates to
one, annihilates exactly `ker(f)`, and generates its complement:
`ker(f)=(1-E)`. Normality and flatness of the source, Noetherianity of
the base, and integral-evaluation surjectivity are not assumptions.

For the marked normal closure, the new
`normalizationTensorEvaluation_span` derives generic spanning from the
existing evaluator square and generic surjectivity. The actual finite
normal etale intermediate model supplies the finite etale structure
on the existing `P_B`. `NormalizationIntegralFactor.lean` constructs
`r_B` and `E_m=r_B(1)` and identifies `P_B/(1-E_m)` with the original
`T` by the original evaluator, including its formula on every quotient
representative. This makes `T` finite. The kernel formula and actual
surjectivity identify `T` with localization away from `E_m`, giving
whole-ring etaleness. Under separability, the comparison with the
previous generic selector is `β_Σ(1⊗E_m)=e_m`. The integral construction
itself adds no separability premise, new field marking, tensor carrier,
second normalization model or factor-selection hypothesis.

The checked primary source [Stacks, Lemma 10.151.4, Tag
02FL](https://stacks.math.columbia.edu/tag/02FL) supplies the standard
unramified diagonal localization/separability-tensor input only. The
trace construction and actual normalization comparison are direct
project proofs; no literature axiom or new source-input package is used.
All 28 APIs compile without warnings. The full build passes 3198 jobs
with only the two unchanged Challenge warnings. The focused suite and
five fresh neighbors pass 153 examples and 88 enforced standard-three
axiom audits; the focused suite contributes 30 examples, three private
helpers and 28 audits. The unchanged dependency audit passes six primary
contracts and two support reports. The central inventory is 940 checks,
565 examples and 832 reports; its historical prefix is unchanged and was
not rerun in full. The 79-page PDF (826296 bytes), eight-page visual
review and independent mathematical/Lean--TeX reviews pass. The SP80
parity-queue entry records the complete validation.

The focused suite verifies the ring-level specialization to the actual
finite-etale affine inverse image: both section-ring normality inputs
are derived from normal stalks, and the original function fields and
marked normal closure give finite etale normalization without
Noetherianity. Next integrate this result into a
named actual affine normalized-cover constructor and structural-map/
finite-etale morphism endpoints. Overlap compatibility, gluing and the
global finite etale Galois refinement are still required. The earlier
affine-cover constructor retains its stronger normality/Noetherianity
and normal-stalk inputs; deriving those stalk inputs from smooth geometry
and Chow--Betti generation remain separate. All earlier audit text is
preserved unchanged.

## 17. SP81 follow-up: the actual finite etale affine refinement

The checkpoint is proved and validated. For a finite dominant
etale morphism `p:Y -> X` of integral schemes and a nonempty affine
`U`, `FiniteEtaleNormalClosure.lean` constructs the existing
`NormalizedCover` using the original marked function-field normal closure
and actual inverse image `V=p⁻¹U`. Its visible map is the existing
normalization isomorphism. Normal stalks on both `U` and `V` give the
normal section rings; no Noetherian-base premise is needed. The datum
identity is literal and the full-visible boundary separation applies.

The structural maps from the normal-closure normalization to
`Spec Γ(X,U)` and the actual `U` are finite etale. Its constructed
refinement to `V` is the marked normalization leg followed by the
inverse of the existing visible isomorphism. Composing with that
isomorphism recovers the original leg; composing with `p|_U` gives
exactly the chart structural map. The original composite over `X`
is also proved, and the refinement itself is finite etale.
Both actual maps are surjective by lying over. Chart surjectivity needs
only dominance, integral schemes and the nonempty affine chart, without
finiteness, etaleness or normal-stalk premises. Refinement surjectivity
needs finite dominant `p` and normal stalks on `V`, with no etaleness or
base-normality premise. Both normal-stalk hypotheses remain in the
finite-etale endpoints.

Scheme etaleness is transported from the actual intermediate morphism's
local standard-smooth presentations through the finite tensor source.
The two helper APIs are `piTensorProduct_ringHomProperty` and
`piTensorProduct_isEtale`. SP80's evaluation surjectivity and
complementary-idempotent kernel give an open immersion `Spec(ev_B)`
into this source, whose structural composite is therefore etale.
The missing general converse from `Algebra.Etale` to scheme `IsEtale`
is not assumed. No replacement fields, marking, normalization carrier,
cover type or source axiom is introduced.

All 19 APIs compile without warnings in the 2761-job scoped build:
seventeen in the main module and two helpers. The 81-page PDF (831678 bytes) passes
its clean final warning/reference/box scan and visual checks of pages
12, 13, 61, 72 and 78. Independent geometry and Lean--TeX reviews pass.
The focused suite passes 25 examples and 19 enforced standard-three
axiom audits without warnings. Five fresh neighbor suites also pass;
the six suites total 146 examples and 89 enforced audits, with no warnings
or errors. The full build passes 3200 jobs with only the two unchanged
Challenge warnings. The unchanged dependency audit passes six primary
contracts and two support reports. All nineteen API parity checks pass.
The static central inventory is 959 checks, 565 examples and 851 reports;
its historical prefix is unchanged and the historical file was not
re-elaborated. The SP81 parity-queue entry records the complete validation.
Compatibility under localization and on overlaps, cocycle
identities, gluing and the global Galois action remain to be proved.
Deriving normal stalks from smooth geometry and Chow--Betti generation
remain separate. All earlier audit text is preserved unchanged.

## 18. SP82 follow-up: same-ambient localization and actual affine restriction

The checkpoint is proved and validated. The 28 production APIs compile
cleanly in the 2764-job scoped build:
17 generic localization APIs, nine actual-restriction APIs and two
marked normal-closure restriction APIs. The same-element inclusion
between existing integral closures has injectivity and strict
identity/composition and ambient-map naturality. Under compatible base
localization it exhibits the target as the corresponding localization;
the tensor base-change equivalence preserves the original scalar and
ambient inclusion on pure tensors. The ambient action already makes
denominators units. No normality, Noetherianity, finite-degree premise
or replacement field is needed for this algebraic comparison.

The contravariant scheme map has its structural/naturality squares
and generic identity/composition laws. Principal localization gives
an open immersion with the exact inverse-image range. Arbitrary
multiplicative-set localization is not claimed to be an open immersion.
The actual adapter derives section scalar towers, constructs
normalization restriction and its structural squares, proves its
principal-open localization/open-immersion specialization, and proves
naturality of the original whole-preimage normalization isomorphism.

Both the actual structural map and marked refinement commute with
restriction for any nonempty affine `W <= U`, not just principal opens.
The original ambient field, normal closure and marking are unchanged.
The chart square needs dominant `p`; the refinement square also needs
finite `p` and explicit normal stalks on its inverse images. Neither
requires etaleness, base normality or Noetherianity. The existing
`pi_U`, `lambda_U` and visible `nu_{p,U}` are retained; no new cover
carrier, geometric hypothesis package or source axiom is introduced.

The exact checked primary source scopes are integral-closure
localization (0307), principal-localization open immersion (01I3),
and basic-open inverse image (00E2). The paper reuses 0307 and adds
only the 01I3 bibliography entry. The focused suite passes 39 examples
and 28 enforced standard-three axiom audits. Three fresh neighbor
suites also pass; together the four suites have 107 examples and
71 audits, without warnings or errors. The full build passes 3203 jobs
with only the two unchanged Challenge warnings. The fresh unchanged
dependency audit passes six primary endpoint contracts and two support
reports without warnings or errors.

The 81-page PDF (835379 bytes) passes its final clean warning/reference/
citation/box scan and visual review of pages 13, 14, 61, 62, 73, 74 and
81. Independent mathematical/code/Lean--TeX review and all 28 API
parity checks pass. The static central inventory is 987 checks,
565 examples and 879 reports; its byte-identical historical prefix
was not re-elaborated in full. The audit prefix and SP81 queue history
also remain byte-identical to `db8a206`. The parity-queue entry records
the complete validation scope.

The generic self/composition identities are proved, but actual overlap
comparisons, coherence/cocycle assembly, global gluing and the compatible
Galois action remain next. Normal stalks from smooth geometry and
Chow--Betti generation are separate. All earlier audit text is preserved
unchanged.

## 19. SP83 follow-up: coherent actual affine inverse-image opens

Ten production APIs compile cleanly in the 2740-job scoped build.
Actual restriction in the same fixed ambient field has identity,
composition and common-refinement diamond laws. Its structural square
commutes over the original `X`, retaining the original section rings,
generic germs and normalization carriers.

For any nested nonempty affine opens `W <= U`, the actual restriction
is injective on points, is an open immersion, and has exact image
`mu_U^-1(W)`. Common principal neighborhoods in both charts supply
the point lifts and local open immersions. This introduces no
separatedness, affine-intersection, finite-degree, normality or
Noetherianity assumption beyond integral `X` and its fixed field
extension. The exact standard input is Stacks 01IW and its existing
Mathlib counterpart; no new source axiom is introduced.

SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

Next package the nonempty affine-open diagram, its locally directed
common-refinement condition and global gluing, then descend the marked
refinement and Galois action. Formal chain equalities on non-affine
opens are not a geometric-overlap theorem for their global-section
models. Normal stalks from smooth geometry and Chow--Betti generation
remain separate. The complete pre-SP83 audit text is unchanged.
