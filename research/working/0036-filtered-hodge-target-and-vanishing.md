# Filtered rational target and the vanishing comparison

Date: 2026-11-08.

Follow-up: [0037](0037-filtered-projector-defect.md) constructs the algebraic
cyclic filtered detector of the original defect. Its geometric filtered
realization and the boundary-control step below remain open.

## Implemented target

The shared construction is independent of a cycle map. For a rational
vector space H it uses the actual tensor product H_C = ℂ ⊗_ℚ H, its
injective embedding x ↦ 1 ⊗ x, and canonical conjugation on the complex
coefficient. A complex filtration determines the rational subspace

\[
 \{x\in H:1\otimes x\in F^pH_C\cap\overline{F^pH_C}\}.
\]

Rational tensors are fixed by conjugation, so membership is equivalent
to the single F^p test. This observation does not prove purity for an
arbitrary filtration. `PureRationalHodgeStructure H (2*p)` separately
requires finite dimension, a bounded decreasing filtration, and
opposedness in weight 2p. Its type-(p,p) piece and rational target are
derived from these data; there is no supplied Hodge-class field.

| Owner | Construction and scope |
| --- | --- |
| [HodgeFiltration.lean](../../HodgeConjecture/Realization/HodgeFiltration.lean) | Tensor complexification, embedding, conjugation, conjugate subspaces, filtered-map compatibility, pure structures and their diagonal rational targets. Mathlib-only imports. |
| [FilteredHodgeTarget.lean](../../HodgeConjecture/Realization/FilteredHodgeTarget.lean) | Adapter to the existing `RationalHodgeCycleClassModel`. The original cycle map and its type theorem remain explicit; `target_iff` gives the actual filtration-membership statement. |
| [BettiHodgeTarget.lean](../../HodgeConjecture/Realization/DeRham/BettiHodgeTarget.lean) | Transports the actual scheme de Rham filtration to the complexification of actual rational singular cohomology through a specified comparison. No cycles or projective-line examples are imported. |
| [ProjectiveLineHodgeComparison.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLineHodgeComparison.lean) | The existing geometric P¹ filtration supplies a proved pure weight-two instance and specializes the general scheme target. The old target and ordinary cycle map are preserved. |

The P¹ tensor embedding and conjugation now delegate to the shared layer.
Their public API names remain compatibility wrappers. They do not define
new competing complexifications or real structures.

For a general variety, the topological space must still be identified with
its analytic complex points, its geometric period isomorphism constructed,
and the pure-filtration hypotheses proved. Supplying an arbitrary linear
equivalence does not discharge these obligations. General cycle-class
construction, type compatibility, coverage, and the equivalence bridge
remain separate tasks. Tate-twisted period descent is not substituted for
untwisted rational type-(p,p) membership.

## Upstream comparison audit

Inspected the pinned Axiom Stacks revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6` and the current de Rham
candidates at `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
`RealizationComparison.lean` compares module-valued hypercohomology with
underlying abelian sheaves (Stacks 01F1); it is not a singular Betti–de
Rham period theorem. `Comparison/Existence.lean` concerns Garel maps.
The inspected Hodge/characteristic-zero modules still take the relevant
Weil-Betti comparison or Deligne–Illusie hypotheses as explicit inputs.

The sibling AxiomMath/Weil tree at
`27cdb2049be62ee2911429b47f54774078450e32` has useful complex-point
analytic topology and Artin comparison infrastructure. The inspected
Artin comparison relates torsion étale and analytic sheaf cohomology;
it does not construct the required algebraic de Rham–rational singular
comparison. These are candidate components for a later port. No source
proof was imported in this checkpoint, and this candidate audit is not
a proof of absence across every upstream file.

## What the two repos' vanishing arguments actually share

The local Jacobian working tree is
`/Users/chloevandervlugt/Desktop/collision-ideals`. Its sources were read
without editing them. It uses a different main Lean version, so a direct
project import is not an established reuse path.

| Existing argument | Proved endpoint | Missing geometric step |
| --- | --- | --- |
| Jacobian `General/Keller/ConjugateInvariantConormal.lean` | For the actual nonzero boundary ideal b_F in the target polynomial algebra, vanishing of every transported coordinate conormal component is equivalent to b_F being the unit ideal. The finite-generator test uses that same ideal. | Prove stability of this actual boundary ideal under the target derivations. Finite generation and regularity on the retained open do not prove that stability. |
| Hodge [ProjectorClosureDefect.lean](../../HodgeConjecture/Boundary/ProjectorClosureDefect.lean) and [ChowLocalization.lean](../../HodgeConjecture/Inputs/ChowLocalization.lean) | The raw closure's defect Π⋆Π−Π restricts to zero. Localization puts it in the boundary image when the supplied algebra restriction is the actual Chow restriction; actual additive Chow exactness is proved. | Instantiate the multiplicative restriction, then correct the defect or show it vanishes in the compactified correspondence algebra, retaining the required cohomological action. A boundary class need not be zero. |
| Hodge [SupportedClass.lean](../../HodgeConjecture/Realization/Chow/SupportedClass.lean) | Under supported-cohomology localization, a component basis and fundamental-class comparison, vanishing off a chosen support yields an explicit ordinary cycle representing the class. | Construct the support of codimension at least p and the geometric cohomological comparisons for the prescribed class. |

The common research pattern is to identify the actual defect, prove it is
invisible on an open, and then control the remainder along the boundary.
The Jacobian polynomial differential-ideal criterion is a particularly
strong boundary-control mechanism. It is not yet a theorem about an
arbitrary Chow correspondence defect.

There is a precise algebraic version of this common mechanism. Let
R = k[x₁,…,xₙ] in characteristic zero and M be a finite R-module.
Suppose each coordinate partial has an operator on M satisfying the
Leibniz rule. If M becomes zero over Frac(R), then a common nonzero
denominator annihilates M. Its annihilator ideal is stable under every
partial: differentiating a·m = 0 gives (∂ᵢa)·m = 0, since a also kills
the derivative of m. The polynomial differential-ideal criterion then
makes the annihilator the unit ideal, hence M = 0. This is a mathematical
deduction explaining the repo comparison, not a newly formalized theorem.
The decisive input is an operator on the whole finite module, including
the boundary, rather than a connection only after localization.

The [Yun paper, §7](https://arxiv.org/html/2610.22678v1#S7)
offers a related mechanism: an extended Fourier–Mukai family of complexes
of mixed Hodge modules has no twistor-parameter torsion. Its proof uses
truncation closure and support-locus comparison. This motivates a search
for a matching filtered obstruction family, rather than an application
of generic vanishing alone. The paper's parameter direction is distinct
from a normalization divisor in our geometry.

Two controls constrain any proposed bridge. A module R/(t) vanishes
after inverting t but is nonzero. Likewise, under s=t² the target
derivation sends t to 1/(2t); regularity away from t=0 need not extend
across that divisor. The Jacobian object bench already records this
second diagnostic; it is not a Keller counterexample.

An actionable next research test is to choose **one** existing defect
and construct a coherent filtered object whose vanishing detects it.
Then prove compatibility with restriction and a no-torsion or derivation-
stability theorem in the relevant boundary direction. A mixed Hodge
module can itself be supported on a proper subvariety, so belonging to
that category alone would not eliminate geometric boundary support.
Even a successful projector correction would still need the prescribed
Hodge-class action and the target equivalence. This checkpoint adds no
axiom or conditional vanishing package to conceal those steps.
Taking the complexified cokernel of the Hodge cycle map and declaring a
constant flat family would not advance this argument: generic vanishing
of that family is already the desired surjectivity. The family must give
independent geometric information about an existing defect.

Detection also matters at the endpoint. Vanishing of a cohomological
realization of a Chow defect proves only homological triviality unless a
separate detection or correction theorem is available. The cycle-class
map is not assumed injective here. For an arbitrary variety, pushing an
object to its Albanese would likewise require a proof that the relevant
obstruction survives that operation. A proposed family must address the
actual required Chow statement or explicitly use a weaker, sufficient
cohomological endpoint.

## Validation

`FilteredHodgeTargetVerification.lean` checks a proper rational subspace
inside the genuine two-dimensional complexification: (1,0) is selected,
(0,1) is excluded. It also checks filtered-map compatibility and the
actual scheme-filtration membership formula. The P¹ regressions retain
the imaginary class outside the rational lattice and the original
ordinary infinity-class witnesses. Import boundaries enforce independence
of the generic target from cycles, schemes and comparison packages, and
independence of the scheme target from the cycle layer.

The full library build passed (5,103 jobs), as did all import boundaries.
The focused generic target audit passed 15 standard-three axiom checks;
the P¹ structure and geometric comparison suites passed 42 and 33 checks.
The allowed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
The root-import inventory passed with the new generic and scheme target
declarations exported. Local documentation links and `git diff --check`
also passed.
Existing unrelated full-build warnings retain their previous scope.
