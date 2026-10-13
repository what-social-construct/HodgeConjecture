import HodgeConjecture.Correspondence.CollisionEtale
import HodgeConjecture.Correspondence.EtaleClasses
import HodgeConjecture.Correspondence.FiniteCoproduct
import HodgeConjecture.Correspondence.FiniteEtaleModel
import HodgeConjecture.Correspondence.Graph
import HodgeConjecture.Correspondence.GraphSubscheme
import HodgeConjecture.Correspondence.GraphCycles
import HodgeConjecture.Correspondence.GraphComposition
import HodgeConjecture.Correspondence.EtaleGraphIntersection
import HodgeConjecture.Correspondence.GraphSlice
import HodgeConjecture.Correspondence.GraphCycleComposition
import HodgeConjecture.Correspondence.DeckBaseChange
import HodgeConjecture.Correspondence.RelativeProductComparison
import HodgeConjecture.Correspondence.GraphBaseComparison
import HodgeConjecture.Correspondence.GraphCycleBaseComparison
import HodgeConjecture.Cycles.IntegralMultiplicity
import HodgeConjecture.Cycles.ClosedImmersionPushforward
import HodgeConjecture.Cycles.FinitePushforward
import HodgeConjecture.Cycles.GradedFinitePushforward
import HodgeConjecture.Cycles.FiniteGrading
import HodgeConjecture.Cycles.IsomorphismTransport
import HodgeConjecture.Cycles.LocalOrder
import HodgeConjecture.Cycles.LocalOrderLength
import HodgeConjecture.Cycles.LocalOrderNorm
import HodgeConjecture.Cycles.LocalOrderLocalization
import HodgeConjecture.Cycles.LocalOrderNormFormula
import HodgeConjecture.Cycles.LocalOrderTransport
import HodgeConjecture.Cycles.FunctionFieldTransport
import HodgeConjecture.Cycles.FunctionFieldMap
import HodgeConjecture.Cycles.SchemeLocalOrder
import HodgeConjecture.Cycles.Examples.LocalOrder
import HodgeConjecture.Cycles.PointSupport
import HodgeConjecture.Cycles.SupportCodimension
import HodgeConjecture.Cycles.DivisorSupport
import HodgeConjecture.Cycles.OpenSupport
import HodgeConjecture.Cycles.OpenClosedBaseChange
import HodgeConjecture.Cycles.HeightOneFiniteness
import HodgeConjecture.Cycles.RationalFunctionPresentation
import HodgeConjecture.Cycles.DivisorFiniteness
import HodgeConjecture.Cycles.PrincipalDivisor
import HodgeConjecture.Cycles.PrincipalDivisorTransport
import HodgeConjecture.Cycles.DimensionFunction
import HodgeConjecture.Cycles.DimensionFunctionRestriction
import HodgeConjecture.Cycles.CycleDegree
import HodgeConjecture.Cycles.OpenGrading
import HodgeConjecture.Cycles.OpenRestrictionSurjectivity
import HodgeConjecture.Cycles.PrincipalDivisorDegree
import HodgeConjecture.Cycles.PrincipalDivisorImage
import HodgeConjecture.Cycles.PrincipalDivisorRestriction
import HodgeConjecture.Cycles.GradedPushforward
import HodgeConjecture.Cycles.PrincipalRelations
import HodgeConjecture.Cycles.PrincipalRelationRestriction
import HodgeConjecture.Cycles.ChowPushforward
import HodgeConjecture.Cycles.FinitePrincipalDivisor
import HodgeConjecture.Cycles.FiniteChowPushforward
import HodgeConjecture.Cycles.RationalFiniteChowPushforward
import HodgeConjecture.Cycles.ChowOpenRestriction
import HodgeConjecture.Cycles.ChowIsomorphism
import HodgeConjecture.Cycles.SupportDimension
import HodgeConjecture.Cycles.FiniteTypeDimension
import HodgeConjecture.Cycles.FiniteTypeSchemeDimension
import HodgeConjecture.Cycles.LowDimensionalDimensionFunction
import HodgeConjecture.Cycles.Examples.DimensionFunction
import HodgeConjecture.Cycles.TranscendenceDegreeDrop
import HodgeConjecture.Cycles.IntegralDimension
import HodgeConjecture.Cycles.NormalizationDimension
import HodgeConjecture.Cycles.AffineDimension
import HodgeConjecture.Cycles.AffineSupportDimension
import HodgeConjecture.Cycles.PolynomialPrimeHeight
import HodgeConjecture.Cycles.PolynomialMaximalHeight
import HodgeConjecture.Cycles.PolynomialClosedPointDimension
import HodgeConjecture.CommutativeAlgebra.IntegralIdealPolynomial
import HodgeConjecture.CommutativeAlgebra.MonicPrimeCoefficients
import HodgeConjecture.CommutativeAlgebra.NormalGoingDown
import HodgeConjecture.Cycles.NormalizationLocalDimension
import HodgeConjecture.Cycles.AffineClosedPointDimension
import HodgeConjecture.CommutativeAlgebra.GenericFiberAlgebra
import HodgeConjecture.CommutativeAlgebra.ResidueLocalization
import HodgeConjecture.Cycles.ResidueNormalizationLift
import HodgeConjecture.Cycles.ResidueNormalizationLocalization
import HodgeConjecture.Cycles.LocalizationTranscendenceDegree
import HodgeConjecture.Cycles.AffinePrimeDimension
import HodgeConjecture.CommutativeAlgebra.PrimeQuotientCover
import HodgeConjecture.Cycles.ConsecutivePrimeDimension
import HodgeConjecture.Cycles.AffineDimensionFunction
import HodgeConjecture.Cycles.AffineSchemeDimensionFunction
import HodgeConjecture.Cycles.StructuralResidueField
import HodgeConjecture.Cycles.AffineResidueField
import HodgeConjecture.Cycles.AffineResidueFieldDimension
import HodgeConjecture.Cycles.AffineSchemeResidueDegree
import HodgeConjecture.Cycles.ChartResidueDegree
import HodgeConjecture.Cycles.FieldDimensionFunction
import HodgeConjecture.Cycles.FieldSupportDimension
import HodgeConjecture.Cycles.IntegralCodimension
import HodgeConjecture.Cycles.PrincipalRelationCodimension
import HodgeConjecture.Cycles.RationalChow
import HodgeConjecture.Cycles.CoefficientRestriction
import HodgeConjecture.Cycles.RationalChowOpenRestriction
import HodgeConjecture.Cycles.RationalChowIsomorphism
import HodgeConjecture.Correspondence.TransposeAlgebra
import HodgeConjecture.Correspondence.ProjectorDefect
import HodgeConjecture.Correspondence.ProjectorLift
import HodgeConjecture.Correspondence.Examples.SplitPoints
import HodgeConjecture.Correspondence.Examples.SplitPointMaps
import HodgeConjecture.Correspondence.Examples.SplitIntegralSubschemes
import HodgeConjecture.Correspondence.Examples.SplitCycleGeometry
import HodgeConjecture.Correspondence.Examples.SplitProductGeometry
import HodgeConjecture.Correspondence.Examples.SplitPointMultiplicity
import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry
import HodgeConjecture.Correspondence.Examples.SplitSpanCoproduct
import HodgeConjecture.Correspondence.Examples.SplitGaloisSheets
import HodgeConjecture.Correspondence.FiniteGroupProjector
import HodgeConjecture.Correspondence.GroupAlgebraProjector
import HodgeConjecture.Correspondence.HeckeProjector
import HodgeConjecture.Correspondence.GaloisCollision

/-!
# Scheme correspondences and algebraic projector lifting

This umbrella module collects the layer between collision schemes and
Chow/cohomological realization:

1. scheme correspondences as spans over a base;
2. fiber-product composition and the diagonal identity;
3. strict convolution on isomorphism classes;
4. the free rational span algebra;
5. the finite étale convolution submonoid and its free rational algebra;
6. transpose as a convolution-reversing involution, sending graphs to inverse graphs;
7. an admissible finite-étale realization interface, additive on finite
   coproducts and multiplicative for convolution;
8. collision decompositions as additive correspondence decompositions;
9. graph correspondences attached to deck transformations;
10. finite-group averaging idempotents and their algebraic-projector lifts;
11. arbitrary rational group-algebra idempotents and finite decompositions;
12. subgroup Hecke corners and normalized double-coset operators;
13. explicit Galois collision decompositions as finite coproducts of graphs;
14. normalized collision classes as convolution projectors;
15. algebraic lifts of cohomological projectors and diagonal decompositions.
16. actual split-point scheme spans and their convolution idempotence.
17. finite split-span morphisms, intrinsic points, and actual pullback/coproduct comparisons.
18. integral closed subschemes of finite split schemes, classified as reduced rational points,
    and dimension-zero/no-curve theorems for actual closed immersions.
19. actual split products, point fibers, ideal-sheaf images and inverse images,
    and degree/length-one comparisons through actual residue and stalk maps.
20. actual split finite-group torsors, homogeneous sheet maps, and the regular
    torsor's collision decomposition into deck graphs.
21. actual closed graph morphisms and their defining ideal-sheaf subschemes
    for deck transformations of separated structural morphisms.
22. integral graph cycle generators, their dimension, and rational linear
    assembly into finite cycles on the actual relative product.
23. actual graph intersections in the relative triple product, their
    isomorphic projection onto the composite graph, and ambient generic
    stalk length one for integral closed subschemes.
24. closed-support degree-one cycle pushforward and the actual graph-slice
    pull–push formula, with open-and-closed graph geometry for étale covers.
25. closed comparison with products over a separated structural base,
    preserving actual graph/intersection cycles and the full cycle slice maps.
26. signed local divisor coefficients from actual stalk quotient lengths,
    with function-field, point, and coefficient transport under scheme isomorphisms.
27. reduced point closures and actual integral closed supports, their
    codimension-one identification, and geometric support/coefficient transport.
28. affine numerator/denominator bounds, local finiteness of actual prime
    supports, and finite coefficient support under quasi-compactness.
29. actual finite principal-divisor cycles, their multiplicative-to-additive
    homomorphism, and compatibility with the existing geometric cycle maps
    through scheme isomorphisms.
30. explicit dimension functions, their actual closed-immersion restriction,
    homogeneous submodules of the existing cycles, and the one-lower-degree
    principal-divisor theorem on integral carriers and their ambient images.
31. actual principal relations on Noetherian schemes with an explicit
    dimension function, their finite-sum characterization and Chow quotient,
    and proved descent of closed pushforward and scheme isomorphisms.
32. actual carrier dimension as point height, finite-dimensionality for
    finite-type schemes over a field, and the canonical dimension function
    in dimension at most one, with carrier grading and an affine-line example.
33. strict transcendence-degree drop under proper domain quotients,
    integral-extension dimension invariance and Noether normalization,
    giving the exact finite-type domain dimension formula and the actual
    affine point-closure/residue-field comparison.
34. actual constant-polynomial prime extension and its strict step below
    every maximal ideal, giving full polynomial maximal height and actual
    maximal-localization and closed-point stalk dimension over any field.
35. ideal-controlled monic annihilators and normal-base going down for
    actual integral injections of domains, giving prime-height comparison
    through Noether normalization and full maximal-localization and
    closed-point stalk dimension for every finite-type domain over a field.
36. lifted normalization of an actual prime quotient and localization at
    its nonzero polynomial denominators, constructing a finite-type algebra
    over the polynomial fraction field and a maximal extended prime with
    unchanged contraction and height; for a domain, the original prime
    height equals transcendence degree over this new coefficient field.
37. full cardinal transcendence-degree invariance under actual domain
    localization, and the original-field prime dimension formula for
    finite-type domains through the compatible polynomial fraction-field
    tower, with actual quotient, residue-field and prime-localization forms.
38. actual quotient-spectrum transport of consecutive prime pairs,
    proving height one of the upper prime modulo the lower prime and the
    exact unit drop in quotient and residue-field transcendence degrees
    and quotient dimensions, including reducible finite-type algebras.
39. actual dimension functions on finite-type affine spectra and on affine
    schemes with a locally finite-type structural morphism to a field,
    proving both specialization laws and identifying support degrees and
    fundamental-cycle homogeneity with actual carrier dimensions.
40. independently derived structural base actions on actual scheme residue
    fields, natural residue algebra maps and open-immersion equivalences,
    and the affine stalk-induced algebra comparison identifying the existing
    spectrum dimension function with its actual scheme residue-field degree.
41. structural residue-degree finiteness and the existing dimension-value
    comparison on arbitrary affine schemes locally of finite type over a
    field, with base-compatible transport through the canonical affine
    isomorphism and agreement under affine open immersions.
42. pointwise structural residue-degree finiteness on arbitrary schemes
    locally of finite type over a field, identifying existing affine-chart
    dimension values with ambient residue degrees and proving agreement
    of two charts at points with the same actual ambient image.
43. the global structural residue-degree dimension function on any scheme
    locally of finite type over a field, with both specialization laws
    proved in a common actual affine chart, equality to the existing
    affine construction and value compatibility under open immersions.
44. identification of the global dimension function with actual finite
    point height and reduced point-closure dimension, actual integral
    carrier degrees and fundamental-cycle homogeneity, and point-height
    invariance under open immersions in the locally finite-type field setting.
45. the actual integral codimension formula: finite chain codimension plus
    carrier dimension equals ambient dimension, with degree d-n detecting
    actual codimension n on supports, fundamental cycles and all finite
    cycles in the existing homogeneous submodule.
46. codimension indexing of the existing principal-relation data, preserving
    the actual carrier, function and ambient divisor; empty relation data
    in generic degree for any integral scheme with a dimension function,
    vanishing of its Noetherian relation span, and an equality criterion
    for rational equivalence in that degree.
47. actual degree-weighted finite-morphism pushforward on the existing cycles,
    with positive function-field degrees, agreement with closed immersions,
    restriction to explicitly compatible gradings and coefficient extension.
48. algebraicity of the actual residue-field maps of finite morphisms,
    preserving the original structural transcendence degrees and canonical
    field-induced grading used by that same cycle pushforward.

The free span algebra is not identified with a Chow ring. General proper
cycle extraction, flat/Gysin operations and their rational-equivalence
descent, and compatibility with refined intersection remain geometric
inputs to a `FiniteEtaleAlgebraModel` (or to another explicitly chosen
admissible system). The constructed closed-pushforward quotient is additive;
it does not supply Chow convolution or its target realization.
The affine dimension-function construction is now proved in all dimensions.
Structural residue-field compatibility and open-immersion degree invariance
are also proved, as are the structural residue-degree values on arbitrary
affine schemes and their agreement under affine open immersions. Pointwise
finiteness and affine-chart value agreement in a general locally finite-type
ambient scheme are also proved. Common-chart specialization and cover-law
transfer now construct the global field-induced dimension function.
Its values are now identified with actual point height and carrier
dimension, without a global dimension bound. On integral schemes, actual
chain codimension now gives the degree d-n convention in the existing
cycle module. Principal-relation data now have the matching codimension
indexing, and generic-degree relations vanish under the existing quotient
hypotheses. Rational coefficient extension of the general homogeneous
quotient, comparison with the target rational Chow groups, and extension
to pure-dimensional or componentwise targets remain separate steps.
-/
