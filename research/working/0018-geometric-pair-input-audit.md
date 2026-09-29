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

## 20. SP84 follow-up: actual affine diagram and global gluing

The inclusion-ordered `NonemptyAffineChart X` indexes the original
nonempty affine opens and retains their inherited nonemptiness. The
existing normalization models in the same ambient field and their actual
restrictions form `F_N`; the original maps to `X` form the cocone `c_N`.
All arrows are open immersions with the exact SP83 inverse-image range.
Locally directedness is proved, not assumed: equal images in an upper
chart have a common original base point; a common principal neighborhood
gives a smaller affine chart, whose exact range lifts one point, while
injectivity in the upper chart identifies the other image.

The resulting small thin diagram satisfies Mathlib's scheme-gluing
interface. `Z_N = colimit F_N` is an actual scheme, and its canonical
original-chart maps `jmath_U` are open immersions forming an open cover.
The cocone descends to `mu_N : Z_N -> X`, with exact formula
`mu_N jmath_U = mu_U` and actual transition naturality. Two original
chart points agree globally if and only if they lift from one common
smaller chart. Maps from `Z_N` are determined by their restrictions to
the original charts. These are seven diagram APIs and nine gluing APIs.

The hypotheses remain integral `X` and the fixed extension of its
original function field. There is no finite-degree, normality,
Noetherianity or separatedness assumption, nor any requirement that
intersections be affine. Stacks 01JB/01JC are verified background for
scheme gluing; the normalization-specific common-refinement condition
is proved using SP83 and 01IW's existing Mathlib input. No source axiom,
geometric input package or replacement local normalization is added.

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

The next bounded endpoint is the exact global chart image
`range(jmath_U) = mu_N^-1(U)`. Global finite/etale properties under the
appropriate hypotheses, marked refinement and compatible Galois-action
descent, normal stalks from smooth geometry, and Chow--Betti generation
remain separate. No normalization of sections on a non-affine
intersection is identified with the geometric overlap. The full audit
prefix through SP83 remains byte-identical to `5e16059`.

## 21. SP85 follow-up: actual global inverse-image normalization charts

`GluedNormalizationChart.lean` proves the global range identity
`range(jmath_U) = mu_N^-1(U)` and its equality-of-opens version.
The constructed original-chart cover lifts a global point into some
`Z_V`; a common principal neighborhood in `U` and `V`, the exact
transition range and inclusion naturality then lift it into `Z_U`.
The converse follows from the original structural formula. This uses
the actual glued scheme, not the normalization of sections over a
possibly non-affine intersection.

The canonical open-immersion comparison gives the actual scheme
isomorphism `e_U : Z_U ~= mu_N^-1(U)`. Both inclusion identities,
the exact restricted structural map to `U`, and compatibility with
every original affine chart restriction are proved. These are seven
public APIs; the local scalar helper retains the original germ-derived
algebra map rather than introducing a new public object.

The hypotheses remain integral `X` and the same fixed extension of its
original function field. No finite-degree, normality, Noetherianity,
separatedness or affine-intersection assumption is added. Stacks 01LH
is verified relative basis-gluing context for the manuscript
`prop:normalization-global-chart`; it is not a source axiom. The actual
global range and comparison morphisms are proved from the existing
construction and Mathlib's open-immersion APIs.

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

The next bounded consumer is target-local `IsAffineHom` and finite/etale
transfer through these exact chart isomorphisms under the appropriate
hypotheses. Marked refinement and compatible Galois-action descent,
global normality, normal stalks from smooth geometry and Chow--Betti
generation remain separate. The complete audit prefix through SP84
remains byte-identical to `2a4a52a`.

The SP84 neighbor verification attempt has no retained final tool output
or saved log after interruption, so its result is unconfirmed and
excluded from this checkpoint's passing counts. The SP84, SP83 and
SP81 verification files are statically unchanged from the baseline;
the earlier recorded results are historical, not fresh reruns.

## 22. SP86 follow-up: target-local properties and actual global finite-etale normal closure

`GluedNormalizationProperties.lean` first proves that the actual
nonempty affine opens cover every scheme, including the empty scheme.
For integral `X` and its original fixed field extension `N`, the exact
SP85 chart comparison `e_U` and structural formula identify any
target-local property of `mu_N` with that property of every original
`pi_U : Z_U -> U`. Both schemes in `pi_U` are affine, so `mu_N` is an
affine morphism without a finite-degree or normal-base assumption.
Finiteness and scheme etaleness each have the same exact chartwise
equivalence. These account for five public APIs.

The sixth API in `FiniteEtaleGluedNormalClosure.lean` proves finite
etaleness of the actual global normal-closure map. Its data are
dominant finite etale `p : Y -> X`, integral `X` and `Y`, and explicit
integrally closed stalks on both schemes. The fixed
`N_p = normalClosure K(X) K(Y) (AlgebraicClosure K(Y))` retains the
actual generic map induced by `p`. SP81's finite-etale chart theorem
applies with these stalk inputs; the target-local equivalences give
the two global properties. No replacement normalization carrier,
Noetherian or perfect-field premise, source axiom, or new geometric
hypothesis package is introduced.

The manuscript counterparts are `prop:normalization-target-local`
and `cor:normal-closure-global-finite-etale`. Stacks 01S8, 01WI and
02GJ are verified primary-page locality references. The Lean input is
Mathlib's target-locality and isomorphism transport, combined with
the proved exact map formula; the source citations do not replace
the actual SP81 chart construction.

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

Next descend the marked refinement to `Y` and the compatible Galois
action. Global normality and surjectivity still need checks; normal
stalks from smooth geometry and Chow--Betti generation remain separate.
The complete audit prefix through SP85 remains byte-identical to
`7fca0b4`.

## 23. SP87 follow-up: descent of the original marked refinement

`GluedNormalClosureRefinement.lean` forms a cocone to the actual `Y`
from the original marked chart refinements
`lambda_U : Z_U -> p^-1(U)` and the target-chart inclusions
`iota_(V_U) : V_U -> Y`, where `V_U = p^-1(U)`. The proved actual restriction square gives its
naturality. The existing scheme colimit then supplies the actual
global `lambda : Z_(N_p) -> Y`, with the exact marked chart formulas
`lambda jmath_U = iota_(V_U) lambda_U` and triangle `p lambda = mu_(N_p)`.
Uniqueness is proved for maps satisfying these marked chart formulas,
not for arbitrary maps satisfying only the triangle over `X`.

These are five public APIs. Their hypotheses are integral `X` and
`Y`, finite dominant `p : Y -> X`, and explicitly integrally closed
stalks of `Y` only. There is no etaleness or normal-stalk input on `X`,
Noetherianity or perfectness. The original marked normal-closure
field, actual normalization carriers and germ-derived scalar maps
are retained. The proved restriction compatibility and existing
colimit mapping property suffice; no new source axiom, literature
premise, or geometric input package is introduced. The manuscript
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

Next prove the applicable finite-etale and surjectivity properties of
the refinement and descend the Galois action. The full `G` belongs
to the action over `X`, while only `H` fixing the marked `K(Y)`
preserves `lambda`. This checkpoint does not construct the global
action. Global normality and surjectivity, normal stalks from smooth
geometry and Chow--Betti generation remain separate. The complete
audit prefix through SP86 remains byte-identical to `30fe0ae`.

## 24. SP88 follow-up: finite etaleness of the actual global marked refinement

`FiniteEtaleGluedRefinement.lean` adds two public APIs. The generic
finite-cancellation theorem assumes a finite composite `g f` and
separated `g`, and concludes that `f` is finite. It does not assume
`g` finite, integral schemes, normality, Noetherianity or a field.
The direct Lean proof factors through the graph closed immersion and
a base change of the finite composite. No generic
postcomposition-property instance is introduced.

The actual specialization proves finite etaleness of the existing
`lambda = gluedNormalClosureToCover p hY`, assuming integral `X` and
`Y`, dominant finite etale `p : Y -> X`, and explicitly integrally
closed stalks on both schemes. The SP87 triangle identifies
`p lambda` with the finite-etale `mu_(N_p)` from SP86. Finiteness of
`p` implies separatedness; finite cancellation gives finiteness of
`lambda`, and `IsEtale.of_comp` gives its etaleness. The SP87 map
definition retains its weaker finite-dominant and `hY` hypotheses.

The manuscript counterpart is
`cor:normal-closure-refinement-finite-etale`. The standard finite and
etale cancellation inputs are stated and cited via Stacks 035D and
02GW, whose primary pages were verified. Their source proofs are not
repeated in the manuscript. The property theorem introduces no new
source axiom, re-gluing, chart or carrier replacement, field marking,
or scalar-map change.

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

Next prove surjectivity and descend the compatible Galois action.
The full group acts over `X`; only the subgroup fixing the marked
`K(Y)` preserves `lambda`. Global normality, normal stalks from smooth
geometry and Chow--Betti generation remain separate. No new global
action, surjectivity, global normality or Hodge case is asserted by
SP88. The complete audit prefix through SP87 remains byte-identical
to `af73385`.

## 25. SP89 follow-up: surjectivity of the original global normalization and marked refinement

`GluedNormalizationSurjectivity.lean` adds two public APIs with
different minimal scopes. For integral `X` and any field extension
`N` of its original function field, the actual `mu_N : Z_N -> X`
is surjective. The original chart scalar map `B -> IntCl_B(N)` is
injective and integral. Lying over supplies chart surjectivity;
SP86's exact target-local comparison supplies the global result.
No algebraicity or finite degree of `N`, normality of `X`,
Noetherianity or separatedness is assumed.

For finite dominant `p : Y -> X`, integral `X` and `Y`, and explicitly
integrally closed stalks of `Y` only, the original marked
`lambda : Z_(N_p) -> Y` is surjective. The proof chooses an actual
affine neighborhood of the image of a point of `Y`, lifts the point
through SP81's surjective refinement into that entire inverse image,
and applies SP87's exact marked chart formula. It uses neither
etaleness nor normal stalks of `X`. It does not cancel surjectivity
from the structural triangle `p lambda = mu_(N_p)`.

The manuscript counterpart is `prop:normalization-global-surjective`,
which distinguishes the two scopes and records the finite-etale and
surjective consequence under SP86/SP88's stronger hypotheses. Stacks
00GQ supplies the existing lying-over citation. The same fields,
marked maps, normalization carriers and germ-derived scalars are
retained. There is no new source axiom or geometric input package.

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

Next descend the compatible Galois action; the full group acts over
`X`, while only the subgroup fixing the marked `K(Y)` preserves
`lambda`. Global normality, normal stalks from smooth geometry and
Chow--Betti generation remain separate. The complete audit prefix
through SP88 remains byte-identical to `e910f25`.

## 26. SP90 follow-up: compatible global normalization and marked-subgroup actions

`GluedNormalizationAction.lean` adds ten public APIs for integral `X`
and any field extension `N/K(X)`. The existing inverse-ring chart
automorphisms `a_U(sigma)=Spec(sigma^-1)` commute with the actual
restriction maps. Their natural diagram automorphism descends to
`a_N(sigma)` on the same scheme colimit, retaining the exact chart
formula. Compatibility with the base and identity/multiplication
laws give `a_N:Aut_(K(X))(N) -> Aut_X(Z_N)`, with the same underlying
morphisms. No algebraicity, finite degree or separability is required.

`GluedNormalClosureAction.lean` adds five public APIs. The first
proves preservation of the original marked affine normalization leg
for existing `NormalClosureData` and compatible scalar towers:
the inverse of an element fixing the marked intermediate field fixes
it too, so the original ring-map formulas agree. The four actual
consumers need finite dominant `p`, integral `X` and `Y`, and
explicitly integrally closed stalks of `Y` only. They cancel the actual
affine normalization comparison isomorphism, then use SP87's exact
chart formulas and global morphism extensionality to prove
`lambda a_(N_p)(h)=lambda`. This does not cancel `p`. The marked
subgroup action packages over `Y` with the same underlying global
automorphisms as the full action over `X`.

The manuscript counterparts are `prop:normalization-global-action`
and `prop:normalization-marked-action`. There is no etaleness,
normal-stalk premise on `X`, Noetherianity, perfectness, new source
axiom, literature premise or geometric input package. Original
fields, chart carriers and germ-derived scalar maps remain fixed.

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

Next address global normality as a bounded follow-up. Faithfulness,
fiber comparison and torsor or Galois-cover identification remain
separate. Fixing the marked intermediate field is a sufficient
condition for preserving `lambda`, not a converse or full-stabilizer
identification. Normal stalks from smooth geometry and Chow--Betti
generation remain separate. The complete audit prefix through SP89
remains byte-identical to `6b2baba`.

## 27. SP91 follow-up: normal local rings of the original glued normalization

Four public APIs in `GluedNormalizationNormality.lean` prove integral
closedness of the original normalization coordinate rings and affine
stalks, then domain and integral closedness of every global local ring.
The affine APIs allow any commutative `B` mapping to a field `N`.
Integral closure is integrally closed in that field. Pulling back along
its injective fraction-field map proves integral closedness in its own
fraction field, without claiming that the ambient field is that fraction
field. Localization supplies the affine stalk assertion.

For integral `X` and arbitrary `N/K(X)`, every point of the same glued
scheme lies in an original normalization chart. The chart open immersion
induces an actual stalk isomorphism, transferring the two local-ring
properties. This requires no algebraicity, finite degree, separability,
normality of `X`, Noetherianity or separatedness. The actual marked
`N_p` specialization needs no normal-stalk premise on `X` or `Y`.
It retains the original generic germs, field marking, chart carriers
and colimit scheme; no geometric hypothesis package is introduced.

The manuscript counterpart is `prop:normalization-global-normal`.
Normality is expressed as domain and integral closedness of each stalk.
No scheme `IsNormal` class, global `IsIntegral` instance or marked
function-field identification is asserted. The existing source citations
are Stacks Tags 034L and 00GY, with no new source axiom.

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

Next address global integrality and marked function-field comparison.
Faithfulness, fiber comparison and torsor or Galois-cover identification
remain separate. Normal stalks from smooth geometry and Chow--Betti
generation remain separate. The complete audit prefix through SP90
remains byte-identical to `88a5f8b`.

## 28. SP92 follow-up: integrality of the original glued normalization

Four public APIs in `GluedNormalizationIntegrality.lean` prove pairwise
chart intersection, global reducedness, global irreducibility and the
`IsIntegral` instance. Integral `X` and arbitrary `N/K(X)` suffice.
Actual nonempty common affine refinements witness the overlaps through
the original chart maps. Each normalization chart is integral because
its coordinate ring is a subring of `N`. The irreducible open images
cover the global scheme and their pairwise intersections give global
irreducibility. Nonemptiness comes from a base chart. SP91's domain
stalks imply reducedness, and hence integrality of the same carrier.

The manuscript counterpart is `prop:normalization-global-integral`,
with source citations Stacks Tags 01OM and 01ON. No algebraicity,
finite degree, separability, base normality, Noetherianity or
separatedness is assumed. The actual marked `N_p` specialization needs
no normal-stalk hypotheses on `X` or `Y`. Original germs, fields,
markings, chart carriers and the colimit remain fixed. The intrinsic
function field is available without an asserted identification with
arbitrary ambient `N`.

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

Next address marked function-field comparison. Faithfulness,
fiber/torsor comparison, normal stalks from smooth geometry and
Chow--Betti generation remain separate. The complete audit prefix
through SP91 remains byte-identical to `44d8fec`.

## 29. SP93 follow-up: marked function-field comparison and action faithfulness

The checkpoint has 19 public APIs across four production modules.
For integral `X` and finite `N/K(X)`, the original normalization chart
coordinate rings have fraction field `N`. Compose their canonical
fraction-field equivalences with the actual chart generic-stalk
isomorphisms to compare the intrinsic `K(Z_N)` with `N`. Restriction
squares and common affine refinements prove chart independence; the
actual structural generic-stalk map is preserved. The finite-extension
hypothesis belongs to this comparison, not to SP91/SP92's broader
normality and integrality statements.

The original action was built from inverse ring automorphisms, so its
pullback comparison is `e(a_sigma^* b) = sigma^{-1}(e(b))`. Surjectivity
of `e` yields faithfulness of this same action. No reconstruction of
arbitrary deck transformations, full deck-group equivalence, fiber or
torsor assertion is included.

For the original `N_p` of finite dominant `p : Y -> X`, integral
`X/Y` and normal stalks of `Y` suffice for
`e(lambda^* c) = (functionFieldNormalClosureData p).embedding c`.
The proof cancels the original affine-preimage normalization
isomorphism and uses the exact marked chart formula. No normality of
`X`, etaleness, separability, Noetherianity, replacement field or new
marking is supplied. The manuscript counterparts are
`prop:normalization-function-field-comparison` and
`cor:normalization-marked-function-field`. Existing Stacks Tag 0307
supports only the fraction-field reduction, not a deck-group comparison.

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

Next reconstruct arbitrary deck transformations and compare the full
deck group. Fiber/torsor comparison, the full stabilizer of `lambda`,
normal stalks from smooth geometry and Chow--Betti generation remain
separate. The complete audit prefix through SP92 remains byte-identical
to `cffbb9e`.

## 30. SP94: arbitrary-class recipe condition and normalized descent

The new `Realization/Chow/UpstairsGeneration.lean` uses the independently
specified downstairs Hodge subspace. Its fixed-recipe condition is
`pull (Hdg_X) <= range (clY.comp recipe)`; its indexed condition asks,
for every Hodge class `α`, for an index and coefficient representing
`pull_i α`. The family of maps is fixed before `α` is quantified.
Neither condition asserts generation of all upstairs cohomology.

Seven public APIs give the two definitions, the fixed condition's
elementwise equivalence, passage from fixed to indexed generation,
the normalized-cycle formula, and two conditional Hodge endpoints.
They reuse `RationalDegreeTransfer HY HX` with its positive degree and
push-pull identity. An explicit Chow pushforward and its cycle-class
comparison are required. The downstairs cycle is
`degree_i⁻¹ • pushCH_i (recipe_i c)`. No new projector or marked-Galois
witness package, residual-surjectivity premise, source axiom or unused
scheme morphism is added.

This establishes the conditional implication, not the geometric maps
or recipe generation. The next geometric work remains deck-action
surjectivity/full-group comparison, followed by actual same-cover
Chow--Betti transfer and then generation for the intended `X,p`.
The manuscript gives the precise definition and descent theorem in
section 1, with explicit mathematical hypotheses and no editorial
gap commentary.

The pruning pass begins with dependencies and mathematical consumers.
An object not consumed by the minimal cycle conclusion can still support
a live stronger projector/action endpoint. No module is removed or
archived. The semantic-parity queue records this distinction before any
future bench move. The complete audit prefix through SP93 is preserved
byte-for-byte from `9539dc6`.

SP94 validation passes: 2466-job scoped build; 26 focused examples,
seven declaration checks and seven axiom audits, each with exactly the
standard three axioms; and two new dependency assertions. The latter
confirm that both sufficient-Hodge endpoints consume the degree law
without the normalized projector or declarations from `LinearAlgebra`,
`Boundary` or `Correspondence`. The full build passes 3222 jobs with
only the unchanged Challenge warnings at lines 33 and 46. The unchanged
dependency audit passes six primary contracts and two supporting reports.
No fresh neighbor-suite pass is claimed.

The 92-page PDF (880675 bytes) has a clean final log and passes visual
review of pages 3, 4, 67, 80 and 81. Independent scope review and all
seven API parity checks pass. The central static inventory is 1084
checks, 565 examples and 976 axiom reports; the preserved central prefix
was not re-elaborated in full. The SP93-to-EOF semantic-queue record is
also byte-identical to `9539dc6`.

## 31. SP95: generic extensionality and the full original deck group

Two public generic APIs identify the actual function-field pullback with
the generic-stalk square and prove that it determines a dominant map
between integral schemes over a common base with relatively separated
target. The generic-stalk inclusion is dominant because its image
contains the generic point. Mathlib's existing relative-separatedness
extensionality theorem supplies the equality of actual scheme maps.

Six public normalization APIs use this result on the original integral
glued scheme and its already affine structural map. Uniqueness of deck
transformations needs no finite ambient extension. For finite `N/K(X)`,
the original field comparison gives
`b_N(d)=e_N ∘ (d⁻¹)^* ∘ e_N⁻¹`, which fixes the actual base embedding.
The existing action reconstructs `d`, proving surjectivity. Its previous
faithfulness and the explicit reconstruction give a `MulEquiv` with the
same forward action and the displayed inverse.

No separability, base normality, Noetherianity, etaleness, or finiteness
of the normalization morphism is added. No source axiom, replacement
scheme, field marking or action is introduced. The manuscript's
`lem:generic-pullback-extensionality` and
`thm:normalization-full-deck-group` have these same scopes and maps.
Marked stabilizer converses, fiber/coset and torsor comparisons and
actual Chow--Betti generation remain separate. No object is deleted or
archived. The complete audit prefix through SP94 is preserved from
`05d8601`.

SP95 validation passes the 2327/2780-job scoped builds, 27 focused
examples, eight declaration checks and eight exact standard-three axiom
audits. The 3224-job full build has only the unchanged Challenge warnings
at lines 33 and 46. The unchanged dependency audit passes six primary
contracts and two supporting reports. A fresh SP94 regression passes
26 examples, seven standard-three audits and two direct-descent dependency
assertions, without warnings; no other fresh neighbor-suite pass is claimed.

The 92-page PDF (882837 bytes) has a clean final log and passes visual
review of pages 19, 20, 21, 70 and 83. Independent production, manuscript
and six-document scope reviews and all eight API parity checks pass.
The central inventory is statically 1092 checks, 565 examples and 984
axiom reports; its historical prefix was not re-elaborated in full.
The central and geometric-audit prefixes and the SP94-to-EOF queue
record are byte-identical to `05d8601`.

## 32. SP96: full marked stabilizer and marked deck-group comparison

The six public APIs in `GluedNormalClosureStabilizer.lean` retain the
same finite dominant `p : Y → X`, integral schemes, normal stalks of
`Y`, normal-closure field, original embedding and refinement. They prove
`λ ∘ a_N(σ) = λ ↔ σ ∈ H` and its arbitrary-base-deck counterpart
`λ ∘ d = λ ↔ b_N(d) ∈ H`. The converse uses the actual marked generic
pullback comparison: `σ⁻¹` fixes every element of the embedded `K(Y)`,
and applying `σ` gives pointwise fixedness by `σ`. The other direction
is the existing SP90 preservation theorem.

Viewing a deck transformation over `Y` as one over `X` through
`p ∘ λ = μ`, SP95 reconstructs its field automorphism; the criterion
places it in the original subgroup. The original marked action is
therefore injective and surjective, with an explicit `MulEquiv`
`H ≃ Aut_Y(Z_N)`. Its inverse retains the formula
`b_N(d)=e_N ∘ (d⁻¹)^* ∘ e_N⁻¹`. The promotion over the base and subgroup
membership are private helpers, not replacement public data packages.

The manuscript counterpart is `thm:normalization-marked-stabilizer`.
There is no added etaleness, separability, normal-base, Noetherian or
finite-normalization-morphism hypothesis and no new literature input.
This is not a fixed-field equality, geometric-fiber/coset comparison
or torsor proof. The next geometric checkpoint must fix the actual
fiber, basepoint, coset convention and inverse-pullback action before
proving that comparison. Same-cover Chow--Betti maps and recipe
generation remain separate. No object is deleted or archived; the
complete audit prefix through SP95 is preserved from `864100b`.

The scoped production build passes 2783 jobs and the full build passes
3225 jobs with only the two unchanged Challenge warnings at lines 33
and 46. The focused suite passes 22 examples, six declaration checks
and six axiom audits, every actual axiom set exactly the standard three,
without warnings. Independent production, manuscript and documentation
scope reviews and all six API parity checks pass.

The 93-page PDF (885899 bytes) has a clean final log and passes visual
review of pages 20, 21, 22, 71 and 84. The central static inventory is
1098 checks, 565 examples and 990 axiom reports; its historical prefix
was not re-elaborated in full. Both complete historical prefixes and
the SP95-to-EOF semantic-queue record are byte-identical to `864100b`.

The unchanged dependency audit passes six primary contracts and two
supporting reports. A fresh SP95 regression passes 27 examples, eight
declaration checks and eight axiom audits, each observed set exactly the
standard three, without warnings. No other fresh neighbor-suite pass is
claimed. SP96 is validated.

## 33. SP97: actual generic fiber and affine function-field pushout

The two public APIs in `FiniteFunctionField.lean` and `GenericFiber.lean`
retain a finite dominant `p:Y→X` and integral schemes. The actual affine
section rings, generic germs and function-field embedding form an algebra
pushout: localizing the finite faithful section algebra at the base's
nonzero elements yields the actual upstairs fraction field. The two scalar
towers in the statement are derived locally from the original maps.

Passing to spectra, transporting the original affine-preimage pullback
along its affine presentations, and composing the squares proves that
the actual generic-stalk square is cartesian. Its first leg is the
upstairs generic-stalk morphism, so `IsPullback.isoPullback` gives
`Spec K(Y) ≅ Y ×_X Spec K(X)` with exactly the expected projections.
This standard comparison is not a new public package. The two chart and
generic-germ helpers are private implementation lemmas.

The manuscript counterpart is `prop:actual-generic-fiber`. It distinguishes
generic points `η_X` from their canonical scheme maps `ι_{η_X}`, including
in the existing generic-extensionality proof. No normality, etaleness,
separability, Noetherianity or extra finite-extension premise is added;
there is no new literature input or source axiom.

This is the actual generic fiber, not yet its split base change over `N`,
all geometric fibers, a coset identification or torsor theorem. Next use
the existing tensor/sheet and base-sheet augmentation maps for the generic split fiber,
retaining the marked embedding and inverse-pullback convention. Same-cover
Chow--Betti maps and generation remain separate. No object is deleted or
archived; the complete audit prefix through SP96 is preserved from `e6b06a7`.

Scoped builds pass 2736/2737 jobs for the affine pushout and scheme square.
The focused suite passes 18 examples, two declaration checks and two axiom
audits, each observed set exactly the standard three, without warnings.
Independent production, manuscript and documentation scope reviews and
both API parity checks pass. The 93-page PDF (887663 bytes) has a clean
final log and passes visual review of pages 8, 9, 10, 20, 69 and 81.
The static central inventory is 1100 checks, 565 examples and 992 axiom
reports; its historical prefix was not re-elaborated in full. Both complete
historical prefixes and the SP96-to-EOF queue record are byte-identical
to `e6b06a7`.

The full build passes 3226 jobs with only the unchanged Challenge warnings
at lines 33 and 46. The unchanged dependency audit passes six primary
contracts and two supporting reports. Fresh finite-function-field and
SP96 regressions pass 18 examples/11 axiom audits and 22 examples/six
axiom audits respectively, each actual set exactly the standard three,
without warnings. No other fresh neighbor-suite pass is claimed.
SP97 is validated.

## 34. SP98: tensor base change of the actual generic fiber

The single public API in `GenericFiberBaseChange.lean` uses finite
dominant `p:Y→X` between integral schemes and any commutative
`K(X)`-algebra `E`. It proves the pullback square exhibiting
`Spec(E⊗_{K(X)}K(Y))` as the actual base change along
`Spec E → Spec K(X) → X`, retaining the actual `κ_p` and this tensor
order. The first leg uses the right inclusion followed by the upstairs
generic-stalk map, while the second uses the left inclusion.

The tensor-spectrum square is pasted horizontally with SP97. The standard
`IsPullback.isoPullback` and its projection lemmas provide the canonical
comparison; no public isomorphism wrapper, carrier, marking, action,
private helper or global instance is added. There is no field, finite,
separable, reduced or nontrivial hypothesis on `E`, nor new normality or
etaleness hypothesis on the schemes or `p`.

The manuscript counterpart is `cor:generic-fiber-base-change`, whose
notation `T_E,u_E,v_E,α_E,β_E,θ_{p,E}` records the original maps.
No new literature input or source axiom is introduced. The next step is
the specialization to the original normal closure, its separable
tensor/sheet equivalence and marked base-sheet augmentation. This is not
yet that split comparison, an arbitrary-geometric-fiber or torsor theorem,
or a Chow--Betti generation result. No object is deleted or archived;
the complete audit prefix through SP97 is preserved from `cd3341a`.

The scoped build passes 2738 jobs. The corrected focused suite passes
19 examples, one declaration check and one exact standard-three axiom
audit without warnings. The full build passes 3227 jobs with only the
unchanged Challenge warnings at lines 33 and 46. The dependency audit
passes six primary contracts and two supporting reports. A fresh SP97
regression passes 18 examples, two checks and two exact standard-three
axiom audits; no other fresh neighbor-suite pass is claimed.

Production/manuscript/API parity and the bounded overlap audit pass.
The 94-page PDF (891430 bytes) has a clean final log and passes visual
review of pages 9, 10, 11, 70 and 82. The static central inventory is
1101 checks, 565 examples and 993 axiom reports; its historical prefix
was not re-elaborated in full. Both complete historical prefixes and
the SP97-to-EOF queue record are byte-identical to `cd3341a`. SP98 is validated.

## 35. SP99: the original marked split generic fiber

The four public APIs in `GenericSplitFiber.lean` retain finite dominant
formally unramified `p:Y→X` between integral schemes. The actual `κ_p`
defines the field extension; `functionFieldNormalClosureData p` retains
the original normal closure `N_p`, fixing subgroup and marked embedding.
Formal unramifiedness supplies the already proved actual separability.

The comparison applies `Spec` to the existing tensor/sheet equivalence
and composes with SP98's canonical pullback isomorphism. The projection
to `Y` is the spectrum of the original sheet-embedding map followed by
the generic-stalk map, and the projection to `Spec N_p` is the spectrum
of constants. The old augmentation identity sends the base-sheet point
to the actual pullback lift of the marked embedding and the identity.

The manuscript counterpart is `prop:marked-split-generic-fiber`, with
notation `ψ_p,j_p,c_p,b_H,y_ι`. No new commutative or tensor algebra is
developed, and no field, cover, evaluator, splitting, marking or action
is independently reconstructed. No normal-stalk, Noetherian or perfect-field
input is used. The isomorphism and its map laws are the geometric consumer
of the existing results, not a new target-equivalence package.

Next compare the individual coset points with the original normalization
action. Arbitrary geometric fibers, torsors and same-cover Chow--Betti
realization/generation are not asserted here. No object is removed or
archived. The complete audit prefix through SP98 is preserved from `4cf7b71`.

The scoped build passes 2753 jobs. The corrected focused suite passes
18 examples, four declaration checks and four exact standard-three axiom
audits without warnings. Two transitive declaration checks confirm that
actual separability is upstream of the project splitting/collision
constructions, and that the new isomorphism uses established separability
and the existing tensor equivalence. This is a geometric comparison
checkpoint, not an independent proof of separability from its consequences.

The full build passes 3228 jobs with only the unchanged Challenge warnings
at lines 33 and 46. The endpoint dependency audit passes six primary
contracts and two supporting reports. Fresh SP98/separability regressions
pass 19 examples/one axiom audit and 16 examples/three axiom audits,
respectively; all observed sets are exactly the standard three, without
warnings. No other fresh neighbor-suite pass is claimed.

Independent scope review and four-API Lean--TeX parity pass. The 94-page
PDF (893990 bytes) has a clean final log and passes visual review of pages
23, 24, 70 and 82. The central static inventory is 1105 checks, 565 examples
and 997 axiom reports; its historical prefix was not re-elaborated in full.
Both complete historical prefixes and the SP98-to-EOF queue record remain
byte-identical to `4cf7b71`. SP99 is validated.

## 36. SP100: sheet points and the original normalization action

The four public theorems in `GenericSplitFiberAction.lean` retain the
original normal-closure datum, sheet algebra, evaluation maps, split-fiber
isomorphism and pullback. For any sheet `s`, evaluation followed by SP99
has projections `Spec(D.sheetEmbedding s)` followed by the upstairs
generic map, and the identity on `Spec N_p`. This uses finite dominance,
formal unramifiedness and integrality, not normality.

Using the original normal-stalk hypothesis on `Y`, set
`γ_{N_p}=ι_{η_Z} ∘ Spec(e_{N_p})` with the old field comparison.
The point labelled `gH` then has `Y`-projection
`λ ∘ a_{N_p}(g⁻¹) ∘ γ_{N_p}`. Generic-stalk naturality and the old
action/refinement field identities prove this equality without formal
unramifiedness. The original fixing subgroup identifies the coset's
embedding with `g ∘ ι`. The two projections give the full pullback-point
identity; no new action or point carrier is supplied.

The manuscript counterpart is `prop:split-fiber-sheet-action`, with
notation `ε_s^{N_p}`, `ξ_{p,s}` and `γ_{N_p}`. No public construction,
global instance, new algebra theory or separability proof is added.
Two module-local derived instances provide existing base surjectivity
and the actual function-field algebra. The original normalization and
marked refinement are unchanged; no base-normality, Noetherian or
perfect-field input is added.

This is not a `G`-deck action on `Y` for nonnormal `H`, an unspecified
whole-fiber equivariance statement, a torsor or a Chow--Betti generation
result. The next live work is the actual same-cover cycle/Betti maps,
starting with the finite-cover cycle pushforward and its descent through
principal relations, not a second fiber presentation. No object is removed
or archived. The complete audit prefix through SP99 is preserved from `5b0572c`.

Scoped validation passes 2795 jobs. The corrected focused suite passes
18 examples, four checks and four axiom audits, each observed set exactly
`propext`, `Classical.choice` and `Quot.sound`, without warnings. The full
build passes 3229 jobs with only the unchanged Challenge warnings at lines
33 and 46. The dependency audit passes six primary contracts and two
supporting reports. Fresh SP99/SP93 regressions pass 18/35 examples,
four/19 checks and four/19 axiom audits respectively, each observed set
exactly the standard three, without warnings. SP99's two dependency-direction
checks pass as well. No additional neighbor-suite pass or full historical
central replay is claimed.

Independent production/manuscript/documentation scope review and all four
API parity checks pass. The 96-page PDF (898680 bytes) has a clean final
log and visually checked pages 23, 24, 71 and 84. The central static inventory
is 1109 checks, 565 examples and 1001 axiom reports. Both complete historical
prefixes and the SP99-to-EOF queue record remain byte-identical to `5b0572c`.
SP100 is validated.

## 37. SP101: degree-weighted finite cycle pushforward

The thirteen APIs in `Cycles/FinitePushforward.lean` use the existing
integral support and Finsupp cycle carriers. The generalized image is
literally `W.val.map f`, with generic point `f(ξ_W)`, and equals the old
closed-image object when the latter applies. For a finite support map,
the original `toImage` map is finite and dominant. Its actual generic
pullback, not a replacement field algebra, supplies the positive degree
`d_f(W)=[K(W):K(f(W))]` through existing function-field finiteness.

For finite ambient `f`, linear extension sends `[W]` to `d_f(W)[f(W)]`
over any semiring. It agrees with old closed-immersion pushforward and
the identity. The seven APIs in `GradedFinitePushforward.lean` restrict
the same operation to the existing homogeneous submodules for explicitly
compatible dimension functions, and commute with integral/rational
coefficient extension. Neither ambient integrality nor normality,
dominance, Noetherianity, etaleness or separability is needed.

The manuscript counterpart is `prop:finite-cycle-pushforward`, with
`q_W`, `d_f(W)` and the existing `f_{*,cyc}` notation. The new raw map
extends a previously closed-immersion-only operation by a proved
agreement; it is not a parallel cycle construction. The raw/graded
scope and the explicit degree-comparison premise are retained in TeX.

Next prove the canonical structural-grading comparison and the actual
principal/norm identity before quotient descent. Relation carriers can
be nonnormal inside a smooth ambient scheme; the local law must apply
to their actual Noetherian length-orders. Finite-map composition, flat
pullback/degree, Betti transfer, cycle-class compatibility and generation
remain separate. No source hypothesis package, project axiom or new
commutative-algebra theory is introduced. No object is moved or removed.
The complete audit prefix through SP100 is preserved from `85662d0`.

Raw/graded scoped builds pass 2779/2820 jobs without warnings. The corrected
focused suite passes thirty examples, twenty checks and twenty axiom audits,
every observed set exactly `propext`, `Classical.choice` and `Quot.sound`.
The full build passes 3231 jobs with only the unchanged Challenge warnings
at lines 33 and 46. The dependency audit passes six primary contracts and
two supporting reports. Fresh SP72/SP88 regressions pass 18/20 examples
and eleven/two axiom audits respectively, with exactly the standard three
and no warnings. No additional fresh regression or full historical central
replay is claimed.

Independent scope review and twenty-API parity pass. The final 96-page PDF
(901510 bytes) has a clean log and visually checked pages 40, 41, 75 and 88.
The central static inventory is 1129 checks, 565 examples and 1021 axiom
reports. Both complete historical prefixes and the SP100-to-EOF queue
record remain byte-identical to `85662d0`. SP101 is validated.
