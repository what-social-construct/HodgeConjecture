# Projective-line Betti inputs

Scope checkpoint: 2026-11-06. Focused verification and full integration pass.
This note does not claim a completed singular H² calculation or
a de Rham–Betti comparison. The preceding scheme comparison remains the
result recorded in [0027](0027-projective-line-scheme-comparison.md).

## Actual complex points and their topology

[ProjectiveLineComplexPoints.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineComplexPoints.lean)
starts with actual morphisms `Spec ℂ ⟶ projectiveLine ℂ` over `Spec ℂ`.
It uses the original glued scheme and its two polynomial affine charts.
Each chart point is evaluation of an actual complex-algebra homomorphism;
the chart topology is the regular-function evaluation topology already
identified with the usual complex plane in
[AffineLineComplexPoints.lean](../../HodgeConjecture/Realization/Betti/Examples/AffineLineComplexPoints.lean).

The projective point topology is the final topology of these original
chart maps. Algebraic coverage and the Laurent evaluation on the original
overlap classify the point set as finite complex coordinates plus infinity.
The topological comparison proves that this independently defined
atlas topology is homeomorphic to the native one-point compactification.
Both original affine charts are open embeddings; compactness and the
Hausdorff property follow for this atlas topology.

[OnePointComplexInversion.lean](../../HodgeConjecture/Realization/Betti/Examples/OnePointComplexInversion.lean)
proves the needed native chart transition: zero and infinity are exchanged,
and a nonzero finite coordinate maps to its reciprocal. The continuity
proof uses complex inversion tending to infinity at a puncture and tending
to zero on the cocompact filter. The homeomorphism is its own inverse.

## Actual singular cochains in every degree

[SingularCochains.lean](../../HodgeConjecture/Realization/Betti/SingularCochains.lean)
uses Mathlib's actual singular simplicial set. Degree `n` cochains are all
rational-valued functions on its continuous standard `n`-simplices.
Contravariant precomposition gives a cosimplicial rational module; its
alternating coface complex is the full singular cochain complex.

The differential has the usual `n + 2` faces and signs `(-1)^i`, and its
square-zero identity comes from the singular simplicial identities.
`Cohomology X n` is the categorical homology of this constructed cochain
complex. The concrete quotient is closed cochains modulo incoming
coboundaries, with zero incoming coboundaries at degree zero. Continuous
maps induce pullbacks in the expected contravariant order.

The degree-zero coordinate calculation retains the original face signs
and identifies this full-complex H⁰ with the established
[SingularDegreeZero.lean](../../HodgeConjecture/Realization/Betti/SingularDegreeZero.lean)
model. Constructing H² as an object does not compute it. No dimension,
generator, rational lattice or comparison is supplied as a hypothesis.

## Analytic Laurent periods

[LaurentPeriods.lean](../../HodgeConjecture/Realization/DeRham/LaurentPeriods.lean)
evaluates actual Kähler differentials on the punctured complex line.
Its finite Laurent coefficient function agrees, away from zero, with the
original Laurent algebra evaluation divided by the coordinate. The period
is the actual complex circle integral over the positively oriented unit
circle, rather than a functional defined to equal algebraic residue.

The monomial calculation gives

`integral ω = (2 * π * I) * kaehlerResidue ℂ ω`.

Consequently `dlog T` has integral `2πi`, exact differentials have integral
zero, and division by `2πi` agrees with the algebraic residue coordinate.
This fixes an analytic normalization on the original Laurent forms.

[ProjectiveLinePeriods.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLinePeriods.lean)
uses vanishing on all incoming total Čech boundaries to descend this
integral to the original Čech H², then carries that descended functional
through the proved scheme comparison. Its overlap formula still integrates
the original differential. The actual scheme Chern coordinate has period
`2πi`, and the normalized period of an original rational Chow class equals
its rational degree embedded in `ℂ`.

This is an analytic functional on the actual scheme target with an explicit
representative formula. It does not yet relate that integral to a rational
singular cocycle or an oriented singular cycle, so it is not a singular
de Rham–Betti comparison.

## The next topological theorem spine

The immediate target is the small-chain theorem for a two-open cover.
For a subset `U` of a topological space `X`, define `Sing_U(X)` as the
subcomplex of actual singular simplices whose continuous maps land in `U`.
For an open cover `U ∪ V = X`, form

`smallSing(U,V) = Sing_U(X) ⊔ Sing_V(X)`.

The required new comparison states that its inclusion into `Sing(X)`
induces an isomorphism on chain homology. A concrete construction has
these successive obligations:

1. Construct oriented barycentric subdivision of singular chains and
   prove that it commutes with the actual singular boundary.
2. Construct a chain homotopy from subdivision to the identity, preserving
   chains already contained in each cover member.
3. Prove shrinking of iterated subdivision on standard simplices. Apply
   the Lebesgue number lemma to the pullback cover of each compact simplex,
   and use finite support to subdivide a whole chain sufficiently often.
4. Deduce surjectivity and injectivity of the small-chain homology map.
   Form the short exact sequence for intersection and union of the small
   singular subcomplexes and obtain the actual Mayer–Vietoris sequence.
5. Compute the circle from two contractible arcs and their disconnected
   overlap. Retract the punctured complex chart onto that circle, then use
   the two affine charts to compute the projective-line group. For rational
   cochains, prove the required exact dualization or a chain homotopy
   comparison before transferring results.

For the immediate P¹ H² calculation a bounded subdivision comparison
through chains of degree three and homotopies through degree two may
suffice. All-degree excision is a reusable extension of that obligation.

The simplicial union square is available, but it concerns the small
subcomplex. In general `Sing(X)` is **not** the union of `Sing(U)` and
`Sing(V)`: a singular simplex may cross both opens. Applying the singular
set functor directly to the topological cover pushout therefore does not
establish Mayer–Vietoris. Similarly, sheaf cohomology of the constant sheaf
cannot stand in for singular cohomology without proving their comparison.

After the group calculation, normalization still requires an oriented
circle generator, its relation to the projective-line boundary map, and
a proved bridge from singular chains to the Laurent integral. The
unnormalized comparison has target `H²_sing(X, ℚ) ⊗[ℚ] ℂ`. With compatible
orientation, the intended formula sends the algebraic residue-one class to
`2πi` times the scalar extension of the oriented rational generator. The
sign must be checked against the existing infinity-minus-zero boundary;
it is not fixed by a dimension calculation. A normalized/Tate convention
must state and prove its division by that period explicitly. The rational
lattice must come from the actual singular coefficients and the oriented
generator, rather than an arbitrary transported line inside a complex
one-dimensional vector space.

## Reuse audit and validation boundary

The pinned Mathlib revision already provides
[singular chains](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/SingularHomology/Basic.lean),
[homotopy invariance](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean),
[relative simplicial homology](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean),
and the
[subcomplex intersection/union pushout](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/SimplicialSet/SubcomplexColimits.lean).
The metric
[Lebesgue number lemma](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean)
and
[circle integral formulas](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/CircleIntegral.lean)
are also native.

Its
[simplicial subdivision file](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/SimplicialSet/Subdivision.lean)
defines the subdivision functor and its right adjoint, but does not supply
the chain subdivision, shrinking or small-chain comparison above. No
completed sphere singular-homology calculation, topological singular
excision/Mayer–Vietoris theorem, acyclic-model construction or
realization-to-singular homology comparison was found in the checked
revision. These are outstanding proof obligations.

The separately audited Axiom checkout is the pinned source recorded in
[third-party provenance](../../third_party/axiom-stacks/README.md).
Its algebraic fibre-Betti files concern dimensions of derived algebraic
fibres. No genuine singular-chain sphere computation was found there, so
there is no selected Axiom topological port closure for this step.

The native inversion, all-degree singular-cochain, actual atlas comparison,
and projective-line period modules pass their focused Lake builds.
`make check-projective-line-betti` passes its 3,049-job dependency build,
18 topology examples, five singular-cochain examples and five named
calculations, including actual H¹/H² vanishing for a point, with 66 enforced
standard-three axiom audits. `make check-projective-line-periods` passes its
4,397-job build, 16 analytic/quotient/cycle examples and 16 enforced axiom
audits. All three focused suites have zero errors and warnings.

The full default build passes 4,976 jobs, including cached dependencies.
Root verification passes 1,368 declaration checks, 574 examples and 1,246
axiom reports within `propext`, `Classical.choice`, `Quot.sound`; one report
requires no axioms. The 466 library modules plus the root pass source
scanning. Twelve import boundaries, three indirect-negative checks,
dependency pins, local documentation links and whitespace checks pass.
Existing warning scope remains; the main README remains 69 lines. No new
Hodge-conjecture case or submission candidate follows from these inputs.
