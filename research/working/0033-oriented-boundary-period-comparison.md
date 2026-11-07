# Positive circle pairing and projective-line boundary periods

Scope checkpoint: 2026-11-07. This continues the actual
[circle/P¹ singular calculations](0032-circle-projective-line-singular-cohomology.md).
The cover generator now has proved positive loop pairing. Actual analytic
and singular boundary periods uniquely specify a bounded P¹ comparison,
and its normalized version intertwines independently constructed ordinary
Chow maps. General analytic/Gysin comparison remains a separate obligation.

## Actual chains, cochains and the native connecting sign

[SingularCyclePairing.lean](../../HodgeConjecture/Realization/Betti/SingularCyclePairing.lean)
evaluates original rational simplex functions on native finite chains.
The actual dual differential identity proves Stokes: evaluation of a
coboundary is evaluation on the original boundary. Evaluation therefore
descends to actual positive-degree cohomology on a closed chain. Native
homology representatives retain their literal cochain values, and original
chain maps are adjoint to original cochain pullback. The full/small
comparison pairs with the same actual included chain.

[SubcomplexConnectingRepresentative.lean](../../HodgeConjecture/Realization/Betti/SubcomplexConnectingRepresentative.lean)
specializes native `ShortExact.δ_apply`: lift an overlap cocycle to a pair
cochain, differentiate, and glue its compatible differential to a closed
union cochain. The connecting class is the positive class of that cochain.
Actual lifts and closed representatives exist by the original degreewise
gluing sequence. Native classes are surjective and natural under original
simplicial pullback. [SubcomplexDegreeZeroRepresentative.lean](../../HodgeConjecture/Realization/Betti/SubcomplexDegreeZeroRepresentative.lean)
identifies the native class's H⁰ values with its original constant
zero-simplex values.

## The original positive circle cycle

[CircleOrientedCycle.lean](../../HodgeConjecture/Realization/Betti/Examples/CircleOrientedCycle.lean)
constructs actual singular paths following angles
`−π/2 → π/2 → 3π/2`. The first passes through 1 and lies in the first
punctured-circle chart; the second passes through −1 and lies in the
second chart. Their original native faces give endpoint boundaries that
cancel, both in full singular chains and in the actual small subcomplex.
The small cycle includes as exactly the original full cycle.

[CircleOrientedPairing.lean](../../HodgeConjecture/Realization/Betti/Examples/CircleOrientedPairing.lean)
evaluates the native connecting representative on those two original
one-simplices. The result is the overlap value at the upper endpoint
minus its value at the lower endpoint. The original subtype comparison
and full/small naturality identify these with the original H⁰ coordinates.
Thus `loopPairing_eq_coordinate` proves that the previous H¹ coordinate
is the actual positive-loop pairing. `loopPairing_coverGenerator` is +1.
The verification also proves the positive native cycle has no native
two-chain filling, using this pairing and Stokes.

[LaurentOrientedArcs.lean](../../HodgeConjecture/Realization/DeRham/LaurentOrientedArcs.lean)
proves that the original analytic Laurent integral equals the sum of the
derivative-weighted integrals on `[-π/2,π/2]` and `[π/2,3π/2]`. Native
circle maps are identified with the original complex exponential. A proved
periodic interval-integral shift and adjacent-interval gluing establish
the same actual positive orientation, including its derivative factor.

## Actual P¹ boundary pairing, tensors and ordinary cycles

[ProjectiveLineOrientation.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineOrientation.lean)
uses the original inverse affine-chart connecting isomorphism and actual
radial map to define the positive P¹ boundary-loop functional. It agrees
with the original H² coordinate; the original cover generator has value
one. This functional is not presented as evaluation on a separately
constructed singular fundamental two-cycle.

[ProjectiveLineComplexification.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineComplexification.lean)
uses the genuine tensor product `ℂ ⊗[ℚ] H²_B`. The rational embedding is
`z ↦ 1 ⊗ z`, with injectivity proved. Scalar extension of the actual
positive boundary pairing agrees with the computed tensor coordinate.
The target includes complex coefficients beyond its rational image.

[ProjectiveLineCycleClass.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineCycleClass.lean)
constructs ordinary integral/rational maps from the existing projective-line
Chow quotients into actual rational singular H². The definition is actual
geometric Chow degree times the original singular cover generator. The
previous principal-divisor degree proof supplies relation invariance.
Every reduced closed point maps to that generator; rationalization and
principal relations commute. The original reduced infinity class proves
nonvanishing and rational surjectivity. No de Rham construction is imported
or used to define this map.

## The bounded period comparison and its factor

[ProjectiveLinePeriodComparison.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLinePeriodComparison.lean)
constructs a complex linear equivalence from actual scheme de Rham H²
to the genuine tensor target. The original analytic integral is its
positive boundary-pairing value. That identity uniquely specifies this
map: it is not selected merely from matching dimensions.

On every original overlap form, the tensor coefficient is its actual
Laurent circle integral, also proved equal to the two positive arc
integrals above. The original scheme Chern coordinate maps to `2πi`
times the embedded singular generator. This factor is retained in the
unnormalized ordinary cycle square. The Tate-normalized version divides
by `2πi` and intertwines the independently constructed scheme and singular
ordinary cycle maps on the original rational Chow quotient.

This is a boundary-period comparison for the computed P¹. It does not
construct a general analytic-sheaf integration map, a topological Gysin
map, Poincaré duality or a singular fundamental two-cycle. Identification
with separately constructed general cycle classes and an independent
positive-degree Hodge filtration remain open, as do general variety and
codimension comparisons and prescribed-class coverage. No new Hodge-conjecture
case is claimed. The general characteristic-zero degeneration audit is
unchanged.

## Validation and build boundaries

The pure positive-circle build passes 2,694 jobs; the complete P¹
boundary-period build passes 4,527 jobs. Seven focused suites pass 65
examples, seven named mathematical checks and 154 enforced standard-three
axiom audits, with zero suite warnings and errors. They include actual
native endpoint faces and inclusion, the positive generator pairing, a
proof that the positive native cycle has no filling, reversed analytic
arc signs, point/principal/rationalization formulas, the actual Chow
comparison square, and an imaginary pure tensor outside the rational image.
Build-job counts include reused dependencies.

The full default build passes 5,079 jobs. Root verification passes 1,658
declaration checks, 574 examples and 1,522 axiom reports within `propext`,
`Classical.choice`, `Quot.sound`; one report requires no axioms. Its 92
existing style warnings remain. All 515 library modules plus the root pass
source scans; twenty-two import boundaries, three indirect-negative checks,
dependency pins, local documentation links and whitespace checks pass.
The main README remains 69 lines.

The positive-circle target has 40 project modules and excludes project
scheme geometry, cycles, correspondences, Chow, de Rham and sheaf
cohomology. The P¹ tensor target has 59 modules and the independent
ordinary singular cycle map has 143. The latter includes the existing
Chow normalization/finite-group projector foundation, while excluding
de Rham, sheaf cohomology, Chow realization, collision geometry and graph-Chow
consumers. Pure analytic positive arc integration has four modules and
keeps the existing Laurent-period exclusions. The final period comparison
has 205 modules, intentionally combining these proved constructions.

Independent source reviews confirm that the native sign calculation,
actual tensor target and bounded period scope match the statements.
These working-tree checks retain existing build-warning scope and do not
replace clean-clone or human release sign-offs. Submission candidate
selection and packaging remain unchanged.
