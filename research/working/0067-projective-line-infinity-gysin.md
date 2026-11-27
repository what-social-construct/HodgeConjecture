# Infinity and every-point P¹ Gysin (2026-11-27)

This extends the [finite-point construction](0066-projective-line-finite-point-gysin.md)
to the original infinity point and then to every actual complex-valued P¹ point.
The constructions retain the original glued scheme, native point topology,
singleton H⁰, relative cochains, local Thom class, excision and support forgetting.

[CircleInversion.lean](../../HodgeConjecture/Realization/Betti/Examples/CircleInversion.lean)
defines the actual continuous circle inverse. It preserves the two punctured
circle opens and exchanges their distinguished overlap-component points.
`overlap_coordinates` computes original H⁰ pullback by actual point evaluation.
`cohomologyPullback_inversion` then gives negative identity on native H¹ through
the original Mayer–Vietoris boundary. No square-map proof or Chow class enters.

[SingularMayerVietorisSwap.lean](../../HodgeConjecture/Realization/Betti/SingularMayerVietorisSwap.lean)
uses the actual pair swap in the original cochain short exact sequence.
The existing first-minus-second difference forces negative intersection
reindexing. Original connecting naturality gives `connecting_swap`, including
the full-singular comparison; the sign is not assigned in cohomology coordinates.

[ProjectiveLineReciprocal.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineReciprocal.lean)
conjugates existing one-point complex inversion to `reciprocalHomeomorph` on the
original scheme-valued point space. `reciprocalMap` sends finite z to reciprocal z,
exchanges zero and infinity, and switches the two actual chart opens.
Actual unit-circle inclusion computes overlap H¹ pullback as negative identity.
The overlap sign and boundary-swap sign cancel, giving
`cohomologyPullback_reciprocal_two`: original singular H² pullback is identity.
This proof uses neither Chow/Hodge data nor an earlier global square H² result.

[ProjectiveLineInfinityChart.lean](../../HodgeConjecture/Geometry/ProjectiveLineInfinityChart.lean)
defines `normalChart` by actual affine unit scaling followed by the original
scheme Y chart. `affineSection_normalChart` retains literal evaluation sections
with reciprocal coordinate u*z. The chart preserves its original open range and
base structure, and `normalChart_origin` identifies the original scheme infinity.
This is local algebraic chart data, not a new global scheme inversion morphism.

[ProjectiveLineInfinitySupport.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineInfinitySupport.lean)
retains the actual singleton {infinity}, its finite-chart complement, native
`PointH0`, `pointUnit` and `pointNormalHomeomorph`. The actual complement is
contractible. `pointSupport_scheme_base` binds the same singleton to the original
scheme point `projectiveLineInfinity`, before any cycle class is chosen.

[ProjectiveLineInfinityGysin.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineInfinityGysin.lean)
defines normal-chart points by composing actual scheme evaluation sections with
the actual Y chart. `normalSSetIso_inclusion` and `chartPullback_eq_original`
identify the resulting original simplex maps and relative restriction.
`thomToSupportIso`, `supportedGysin` and `gysin` use original local Thom,
normal-coordinate pullback, relative excision and forgetting in that order.
Actual scaling followed by reciprocal transport compares this independently
constructed supported Thom class with the original zero-supported class.
The native positive H² action gives `gysin_pointUnit`, without using a cycle map
to define or orient the native class. Faithful original support forgetting
proves both supported and absolute independence of the complex unit u.
`every_point_gysinIso` supplies the actual finite or infinity construction as
its witness, with the original singleton H⁰ and positive constant unit.
`every_point_scale_independent` retains these selected-chart families.

[ProjectiveLinePointGysinComparison.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLinePointGysinComparison.lean)
starts with `schemePoint p = schemeMorphism p default`. Its `pointClass p` is
the literal original ordinary quotient map applied to the reduced cycle of
that same scheme image, with the original structural grading.
`pointClass_finite` recovers the existing finite-point class;
`pointClass_infinity` recovers the existing `Infinity.rationalClass`.
`geometric_gysin_unit` compares this unchanged ordinary class with the actual
finite-or-infinity Gysin witness; `pointClass_cycleClass` records normalization.

The certificate family keeps the original full Hodge model and basis, original
square-cover Chow pullback and pushforward, and their original source grading.
`transfer p` uses the cover's GLOBAL finite-flat rank at the selected scheme
image, proved two. This is not an assertion that every local fiber multiplicity
is two. Its native push remains the earlier zero-supported H² trace.
`normalized_cycles` recovers the same original `pointClass p`, including the
original infinity class, from normalized original geometric pushforward.

Coordinate independence here concerns nonzero unit scales in the selected
finite or Y normal chart. Nonlinear atlas-transition naturality, finite-support
additivity and general proper or branched trace remain open extensions.
No new Hodge-conjecture case, higher-dimensional comparison, cryptographic
backend or byte codec is claimed.

The [semantic parity registry](0005-semantic-parity-cleanup.md#proof-role-index-core-objects-and-objects-under-investigation)
and [manuscript proposition `prop:p1-infinity-gysin`](../../paper/main.tex) give
the formal/paper crosswalk. Proof provenance is the repository's original
constructions and pinned Lean/Mathlib APIs; no external theorem text or new
dependency is needed for this extension.

Validation on 2026-11-27: `make check-p1-infinity-gysin` passes
24 controls, 84 distinct enforced standard-three axiom audits and all 162 import
guards. Actual chart maps, support images, native singleton units and original
ordinary classes are retained. The controls compute actual circle H¹ minus and
reciprocal P¹ H² plus, reject omission of the cover-swap sign, exercise negative
and imaginary normal scales, reject a zero scale and reversed unit, and check
the complete point dichotomy. They retain the original full model, basis,
source grading and finite maps; reject unnormalized binding and degree one;
and recover the same original class, including the original infinity class.

Three checked native project proof closures exclude all six old square/local
ramification module origins and all Chow/DeRham declarations. The reciprocal
H² proof additionally excludes the entire absolute P¹ coordinate/generator
module. The checked final project closure excludes all three earlier aggregate
fixtures and all three earlier absolute-square H² results, including private
and generated declarations from excluded origins. All ten required actual
dependencies are present: reciprocal scheme-section evaluation, infinity's
support-to-scheme binding, original Mayer–Vietoris cover swap, native circle
inverse H¹, native reciprocal H², original infinity chart/excision pullback,
both finite and infinity Gysin units, the complete geometric point dichotomy
and original global finite-flat rank. The visibility gate checks all 408
project private-body imports and 6,239 upstream metadata nodes, reading
442 additional exported headers to include omitted private imports.
Missing bodies or any upstream return edge into the project fail the audit.
These gates audit the current formal proof route, rather than minimal
mathematical assumptions.

All three realization exports pass serialized integration builds. The full
public-library build `lake build HodgeConjecture` passes 5,449 jobs. The root
inventory passes 2,466 declaration checks and 574 examples, with 1,858 nonempty
standard-three axiom reports and 1 axiom-free report. All 778 active
library/root/Solution sources pass proof-gap scanning; intentional Challenge
statement placeholders remain separate. Dependency and source pins are
unchanged. Changed-document links and whitespace pass; the manuscript has
161 unique labels and 183 resolved references. The canonical
118-page PDF rebuilds without overfull boxes, undefined references or LaTeX
errors. The changed proposition, proof, scope and declaration crosswalk pass
rendered visual review. Only existing wider-library Lean notices and one
bibliography underfull notice remain. This is cached working-tree validation;
clean-clone and human release sign-offs remain separate.

Canonical source SHA-256:
`a9ad0150cc59f0ab1356d8bc38dbc90634b5d2a1b0801405bc80965b0aac3ec2`.
Canonical PDF SHA-256:
`eceaf17f3907e6a59435db1ccc921ef2ea548ae4ccdaad79b82f0f5843d6c974`.
