# Actual projective-line Hodge filtration and fixed cycle model

Scope checkpoint: 2026-11-07. This continues the actual
[boundary-period comparison](0033-oriented-boundary-period-comparison.md).
The original sheaf de Rham degree filtration now computes the geometric
Hodge filtration on P¹ H². Its bounded period comparison agrees with the
independent type-(1,1) Betti decomposition. The existing fixed-codimension
target predicate is proved for that constructed model, with an explicit
ordinary Chow witness.

## Original degree subcomplexes and derived images

[DegreeFiltration.lean](../../HodgeConjecture/Realization/DeRham/DegreeFiltration.lean)
uses native `HomologicalComplex.stupidTrunc`, restriction and extension.
It retains Kⁿ and its original differential in degrees n ≥ p and has
zero terms below p. Actual inclusion and decreasing transition maps are
constructed, retaining their original term coordinates. Level zero's
inclusion is an isomorphism. Every actual filtered piece starting in
degree at least two is zero for an actual two-term complex.

[TwoTermDegreeFiltration.lean](../../HodgeConjecture/Realization/DeRham/TwoTermDegreeFiltration.lean)
identifies the actual F¹ complex of a two-term complex with its original
degree-one term placed in degree one. The isomorphism preserves the
original `TwoTermComplex.inclusion`. This is a brutal degree filtration;
it does not use the smart truncation's kernel in its boundary degree.

[HypercohomologyFiltration.lean](../../HodgeConjecture/Realization/DeRham/HypercohomologyFiltration.lean)
retains original extension by zero, bounded-below derived functors and
homology. Its maps agree definitionally with the original sheaf
hypercohomology maps. Filtration subspaces are their actual linear ranges.
Monotonicity follows from the original transition factorization, level
zero from the original complex isomorphism, and higher vanishing from
actual zero source complexes. The F¹H² isomorphism follows from the
original two-term derived triangle and its adjacent O-term vanishings.

[SchemeHodgeFiltration.lean](../../HodgeConjecture/Realization/DeRham/SchemeHodgeFiltration.lean)
applies this construction to the original scheme sheaf de Rham complex.
Integer p uses p.toNat because the complex starts at degree zero; every
nonpositive index retains the whole complex. Fᵖ is the actual range of
the original derived inclusion, with no assigned top/bottom subspaces.

## P¹ H² over any field

[ProjectiveLineHodgeFiltration.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLineHodgeFiltration.lean)
uses the previously proved original sheaf-form vanishing above degree one
and actual H¹/H² vanishing of the regular-function term. The actual F¹
map is an isomorphism, retaining the original comparison with H¹(Ω¹).
It follows that

`Fᵖ H² = H²` for `p ≤ 1`, and `Fᵖ H² = 0` for `p ≥ 2`.

The original nonzero scheme Chern coordinate lies in F¹ and not F².
This works over every field and assumes no characteristic-zero or Betti
comparison result. It is a bounded degree-two computation, not a proof
of general Hodge-to-de Rham spectral-sequence degeneration.

## Independent Betti pieces and the geometric filtered comparison

[ProjectiveLineHodgeStructure.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineHodgeStructure.lean)
uses actual rational singular H² and its genuine tensor complexification.
Canonical conjugation conjugates only the complex coefficient, fixing
each rational embedding. The independent type-(1,1) decomposition is
direct, exhaustive and pure of weight two, with an opposed filtration
defined by sums of its pieces. Both actual rational and complex spaces
have dimension one. No cycle-map module, Chow realization or de Rham
source is imported in this layer.

[ProjectiveLineHodgeComparison.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLineHodgeComparison.lean)
proves both raw and normalized bounded period maps preserve all actual
integer filtration levels. It defines the geometric Betti filtration by
mapping the actual derived-image filtration through that original map.
The equality to the independent Betti filtration is proved. Intersecting
the actual transported Fᵖ with its canonical conjugate Fᵠ in weight two
recovers exactly the independently specified pieces; only (1,1) is nonzero.
Rational Hodge classes are the inverse image of this geometric (1,1)
piece under the original pure-tensor embedding.

These definitions use no cycle map. The comparison layer does import the
earlier ordinary-source period module transitively; semantic independence
of the geometric definitions is distinct from the strict import separation
enforced on the pure scheme and independent Betti layers. Canonical tensor
conjugation is also distinct from topological pullback by complex
conjugation on P¹. In particular the raw `2πi` tensor is negated; this
does not change the computed type-(1,1) subspace.

## Fixed-codimension cycle target

[ProjectiveLineHodgeCycleClass.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLineHodgeCycleClass.lean)
instantiates `RationalHodgeCycleClassModel` with the original rational
Chow quotient of zero-dimensional cycles, actual rational singular H²,
the geometric rational Hodge subspace above and the independently
constructed ordinary map. Its target predicate is proved from the
existing actual map's surjectivity. `infinity_class_witness` gives the
explicit rational coordinate of any target class times the original
reduced infinity Chow class. No coverage premise is supplied.

This specializes the existing model under the constructed bounded period
comparison. It does not identify a separately constructed general
topological Gysin/Poincaré-dual map, assert a new classical Hodge-conjecture
case or quantify over other varieties/codimensions. The next concrete
comparison is the geometric point/Gysin normalization. A singular
fundamental two-cycle, general analytic/Gysin comparison, general
characteristic-zero degeneration and general prescribed-class generation
remain open.

## Validation and build boundaries

The pure scheme-filtration build passes 3,159 jobs; the complete
fixed-model build passes 4,537 jobs. The check target separately builds
the native complex/finite-field regression instances (1,226 jobs). Four
focused suites pass 62 examples, ten named mathematical checks and 136
enforced standard-three axiom audits, with zero errors or suite warnings.
They include the native identity-complex regression, actual F¹ inclusion,
nonzero Chern filtration degree in characteristic two, raw-period
conjugation sign, geometric filtration recovery, nonrational imaginary
tensors of type (1,1), and explicit witnesses in the original Chow quotient.
Build-job counts include reused dependencies.

The full default build passes 5,088 jobs. Root verification passes 1,787
declaration checks, 574 examples and 1,651 axiom reports within `propext`,
`Classical.choice`, `Quot.sound`; one report needs no axioms. The 92 existing
root style warnings remain. All 523 library modules plus the root pass
source scans. Twenty-six import boundaries, four indirect-negative checks,
dependency pins, local documentation links and whitespace checks pass.
The main README remains 69 lines.

The native degree-filtration layer has one project module and no other
project imports. Generic scheme image filtration has 11 modules; pure P¹
H² filtration has 55, excluding project cycles, Betti, Chow and
correspondence/collision machinery. Independent Betti Hodge structure has
60 modules and excludes all cycle-map, Chow-realization and de Rham source.
The filtered comparison and final model have 212 and 214 modules,
intentionally combining the original geometric and ordinary-source branches.

Independent source reviews confirm that the actual image filtration,
bounded geometric Hodge comparison and fixed-model quantifiers match
their descriptions. These working-tree checks retain existing warning
scope and do not replace clean-clone or human release sign-offs.
Submission candidate selection and packaging remain unchanged.
