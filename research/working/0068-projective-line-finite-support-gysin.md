# Native finite-support additivity and P¹ Gysin (2026-11-27)

This extends the [every-point construction](0067-projective-line-infinity-gysin.md)
to actual finite supports. Supported cohomology remains the original relative
group Hⁿ(X, X \ F). The finite sum is constructed from original identity maps
of pairs; absolute cohomology coordinates do not define its inverse or Gysin.

[RelativeUnionSplit.lean](../../HodgeConjecture/Realization/Betti/RelativeUnionSplit.lean)
restricts original cochains on the small union, relative to its intersection,
to the two original local relative pairs. Their overlap values vanish, so
`glueFunction` gives the actual inverse. The zero-extension identities yield
`complexIso` and `cohomologyEquiv`. `toUnion_quasiIso` uses original relative
short exact sequences and the existing absolute full-to-small comparison.

[RelativeAdditivity.lean](../../HodgeConjecture/Realization/Betti/RelativeAdditivity.lean)
transports that splitting through original full/small maps and excision for
an actual two-open cover U ∪ V = X. `sumMap` is defined independently as the sum
of original identity-pair extensions Hⁿ(X,U) × Hⁿ(X,V) → Hⁿ(X,U ∩ V).
`sumEquiv_toLinearMap` and `sumMap_bijective` prove that this same sum is an
isomorphism. The result holds in every degree without a class normalization.

[SingularSupports.lean](../../HodgeConjecture/Realization/Betti/SingularSupports.lean)
defines `Supported X F n` by the literal complement subcomplex and `extension`
by original identity relative pullback for F ⊆ G. Self, composition and original
forgetting laws retain these actual maps. For a finite support in a T1 space,
`assemble` sums the original singleton extensions. Finite insertion uses the
open complements of disjoint singleton and remaining supports, then the binary
sum theorem. `assemble_bijective`, `assembleEquiv` and `assembleIso` hold in
every degree, including empty support, whose relative cochains are zero.
`forget_assemble` is the sum of original singleton forget maps; no injectivity
of absolute forgetting is used to establish the finite decomposition.

[SingularFiniteSupport.lean](../../HodgeConjecture/Realization/Betti/SingularFiniteSupport.lean)
retains native singular H⁰ of the actual finite subspace. T1 finiteness gives
its actual discrete topology. `coordinates` evaluates original zero-cocycles
at the same points; genuine `deltaClass` classes reconstruct every native class.
`pointRestriction` is actual continuous singleton pullback, with its proved
scalar-unit formula. `sumCoordinates` records total mass, and constant mass is
the actual support cardinality times the constant. Empty support has zero H⁰.

[ProjectiveLineSupportedPoint.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineSupportedPoint.lean)
uses indexed `Chart p` data to select the actual finite or infinity normal
chart, not a preimage of an absolute generator. `isoOfChart` composes native
singleton H⁰, local Thom and original chart/excision isomorphisms at unit scale.
At infinity, `infinityCochainIso` is original identity pullback between the two
proved equal descriptions of its complement. `gysinIso p` therefore targets
the literal relative group for X \ {p}. Its original forgetting sends the
constant singleton unit to the previously normalized positive generator.

[ProjectiveLineFiniteSupportGysin.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineFiniteSupportGysin.lean)
defines `componentMap` from actual singleton restrictions and these actual
point-supported Thom maps. `supportedGysin` is their canonical support sum.
`gysinEquiv_apply` identifies the forward equivalence with that same definition;
`supportedGysin_bijective` follows from native relative decomposition, not from
absolute forgetting. After forgetting, `gysin_apply` is total mass times the
original positive absolute class. Distinct delta contributions remain distinct:
`supported_difference_ne_zero` proves their balanced difference is nonzero in
the supported target, while `forget_difference_zero` proves its absolute image
is zero. `forget_not_injective` records this obstruction for distinct points.

[ProjectiveLineFiniteSupportComparison.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLineFiniteSupportComparison.lean)
forms `pointRepresentative p` from the same actual scheme image
`schemeMorphism p default`. `cycle S z` is the weighted sum in the original
homogeneous ordinary cycle group. Only then does `classMap` apply the original
rational Chow quotient, retaining the structural grading and representatives.
`supported_cycleClass_comparison` compares original support forgetting of the
native finite Gysin equivalence with that unchanged weighted cycle class.

For nonempty S, `supportUnit` is original constant one on the whole support.
`averageCycle` divides the raw sum of all its point representatives by S.card;
`averageClass` applies the same ordinary quotient. The selected point is used
only to evaluate the original square cover's global finite-flat rank, proved
two independently of that selection. It neither chooses nor replaces the cycle.
The certificate keeps the same full Hodge model, basis, original square Chow
maps and source grading. Its native push is the earlier zero-supported H² trace.
`normalized_cycles` recovers the same original average class. Global rank two
does not assert local multiplicity two at every point of a square-map fiber.

Empty support cannot supply the nonzero full-target column. For zero total
mass, the weighted cycle has zero cycle-class image and cannot equal the
positive target generator. No theorem that its ordinary Chow class is zero
is asserted here. Supported balanced classes can nevertheless be nonzero.

This adds genuine finite-support additivity and its geometric P¹ comparison.
Nonlinear coordinate-transition naturality, general proper or branched native
trace and comparisons on other varieties remain separate. No new Hodge-
conjecture case, cryptographic backend or byte codec is claimed.

The [semantic parity registry](0005-semantic-parity-cleanup.md#proof-role-index-core-objects-and-objects-under-investigation)
and [manuscript proposition `prop:p1-finite-support-gysin`](../../paper/main.tex)
give the formal/paper crosswalk. Proof provenance is the repository's original
cochains, chart/Thom constructions and pinned Lean/Mathlib APIs; this extension
requires no external theorem text or new dependency.

Validation on 2026-11-27: `make check-p1-finite-support-gysin` passes
28 controls, 100 distinct enforced standard-three axiom audits and all 168
import guards. Controls retain actual H⁰, literal singleton restrictions,
native delta classes, original support extensions and the canonical finite
assembly. Empty native source and target are zero. The zero/infinity balanced
class is nonzero in original supported H², has zero forgotten class, and
proves that forgetting is not injective. No supported injectivity argument
uses forgetting. The original weighted cycle, quotient map, full Hodge model,
basis, source grading and finite maps are retained. Empty support and
zero-total weighted classes fail the unit target-column condition; nonempty
unit averages and normalized original geometric pushforward recover the same
original average class. These are cycle-class statements, without asserting
that an arbitrary zero-total ordinary Chow class is zero.

Four checked native project proof closures and the final aggregate closure
pass their exclusion gates. Generic assembly excludes geometry, Gysin and
Chow/de Rham origins. Supported bijectivity and balanced nonzero proofs exclude
the absolute P¹ coordinate module and all three specified forget/absolute-Gysin
symbols, as well as old square and Chow/de Rham routes. The final endpoint
excludes all four older aggregate fixtures and three old absolute-square H²
results, including their private/generated declarations. All thirteen
required actual dependencies occur: original cochain gluing, relative sum-map
bijectivity, canonical finite assembly, original point restriction/evaluation,
actual point-chart Thom data, supported Gysin comparison, original raw cycle,
original rational quotient, unit mass and original global cover rank.
The visibility gate checks all 415 project private-body imports and
6,239 upstream metadata nodes, reading 442 additional exported headers
to include omitted private imports. Missing bodies and upstream return edges
into the project fail the audit. These gates describe the current formal proof
route, rather than minimal mathematical assumptions.

All three realization exports pass serialized integration builds. The full
public-library build `lake build HodgeConjecture` passes 5,456 jobs. The root
inventory passes 2,516 declaration checks and 574 examples, with 1,858 nonempty
standard-three axiom reports and 1 axiom-free report. All 785 active
library/root/Solution sources pass proof-gap scanning; intentional Challenge
statement placeholders remain separate. Dependency and source pins are
unchanged. Changed-document links and whitespace pass; the manuscript has
163 unique labels and 186 resolved references. The canonical
121-page PDF rebuilds without overfull boxes, undefined references or LaTeX
errors. Changed proposition, proof, scope and declaration-crosswalk pages pass
rendered visual review. Only existing wider-library Lean notices and one
bibliography underfull notice remain. This is cached working-tree validation;
clean-clone and human release sign-offs remain separate.

Canonical source SHA-256:
`c81459f4bb75b5c3429bd3ae526624d650a110d1f1be64828c5e3314b690880f`.
Canonical PDF SHA-256:
`44e757c8cc4c8dbf9137afdbcca2347035fea339e4846594a9bae30bed2043d0`.
