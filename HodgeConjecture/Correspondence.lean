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
import HodgeConjecture.Cycles.IsomorphismTransport
import HodgeConjecture.Cycles.LocalOrder
import HodgeConjecture.Cycles.LocalOrderTransport
import HodgeConjecture.Cycles.FunctionFieldTransport
import HodgeConjecture.Cycles.SchemeLocalOrder
import HodgeConjecture.Cycles.Examples.LocalOrder
import HodgeConjecture.Cycles.PointSupport
import HodgeConjecture.Cycles.SupportCodimension
import HodgeConjecture.Cycles.DivisorSupport
import HodgeConjecture.Cycles.HeightOneFiniteness
import HodgeConjecture.Cycles.RationalFunctionPresentation
import HodgeConjecture.Cycles.DivisorFiniteness
import HodgeConjecture.Cycles.PrincipalDivisor
import HodgeConjecture.Cycles.PrincipalDivisorTransport
import HodgeConjecture.Cycles.DimensionFunction
import HodgeConjecture.Cycles.DimensionFunctionRestriction
import HodgeConjecture.Cycles.CycleDegree
import HodgeConjecture.Cycles.PrincipalDivisorDegree
import HodgeConjecture.Cycles.PrincipalDivisorImage
import HodgeConjecture.Cycles.GradedPushforward
import HodgeConjecture.Cycles.PrincipalRelations
import HodgeConjecture.Cycles.ChowPushforward
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

The free span algebra is not identified with a Chow ring. General proper
cycle extraction, flat/Gysin operations and their rational-equivalence
descent, and compatibility with refined intersection remain geometric
inputs to a `FiniteEtaleAlgebraModel` (or to another explicitly chosen
admissible system). The constructed closed-pushforward quotient is additive;
it does not supply Chow convolution or its target realization.
The higher-dimensional finite-type dimension-function construction still
needs the immediate-specialization dimension formula; finite-dimensionality,
strict monotonicity and the affine global/maximal-local dimension
equalities do not supply that law or the uniform maximal-chain theorem.
-/
