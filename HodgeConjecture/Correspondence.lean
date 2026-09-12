import HodgeConjecture.Correspondence.CollisionEtale
import HodgeConjecture.Correspondence.EtaleClasses
import HodgeConjecture.Correspondence.FiniteCoproduct
import HodgeConjecture.Correspondence.FiniteEtaleModel
import HodgeConjecture.Correspondence.Graph
import HodgeConjecture.Correspondence.TransposeAlgebra
import HodgeConjecture.Correspondence.ProjectorDefect
import HodgeConjecture.Correspondence.ProjectorLift
import HodgeConjecture.Correspondence.Examples.SplitPoints
import HodgeConjecture.Correspondence.Examples.SplitPointMaps
import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry
import HodgeConjecture.Correspondence.Examples.SplitSpanCoproduct
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

The free span algebra is not identified with a Chow ring.  Proper cycle
extraction, rational equivalence, and compatibility with refined
intersection remain geometric inputs to a `FiniteEtaleAlgebraModel` (or to
another explicitly chosen admissible system).
-/
