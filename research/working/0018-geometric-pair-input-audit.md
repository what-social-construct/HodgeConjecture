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
