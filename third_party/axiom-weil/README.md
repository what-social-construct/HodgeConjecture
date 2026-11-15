# Axiom Weil source attribution

Selected definitions and proofs in this project adapt
[AxiomMath/Weil](https://github.com/AxiomMath/Weil) at revision
[`27cdb2049be62ee2911429b47f54774078450e32`](https://github.com/AxiomMath/Weil/commit/27cdb2049be62ee2911429b47f54774078450e32).
Weil is Axiom's Weil-conjectures formalization, built on the separate
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) library. Direct
adaptations from Stacks are recorded in the
[Stacks attribution](../axiom-stacks/README.md).

The paths below are relative to the pinned Weil repository. Each project
file also records its source and the scope of its adaptation.

| Project file | Upstream source and retained scope |
| --- | --- |
| `HodgeConjecture/Geometry/ComplexPoints.lean` | [Weil/Definitions.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Definitions.lean), complex-points section only; [Weil/Defs/AlgebraicGeometry/ComplexPoints/AnalyticTopology.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Defs/AlgebraicGeometry/ComplexPoints/AnalyticTopology.lean), topology proofs |
| `HodgeConjecture/Geometry/ComplexPointsFunctoriality.lean` | [Weil/AlgebraicGeometry/ComplexPoints/Functoriality.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/Functoriality.lean), evaluation, affine coordinates, functoriality and open/closed immersion proofs |
| `HodgeConjecture/Geometry/Holomorphic/Forms.lean` | [Weil/Geometry/Manifold/Sheaf/HolomorphicCohomology.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Geometry/Manifold/Sheaf/HolomorphicCohomology.lean), local extension-by-zero helper only; generalized to native form coefficients |
| `HodgeConjecture/SheafCohomology/LocalExactness.lean` | [Weil/Geometry/Manifold/Sheaf/Holomorphic.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Geometry/Manifold/Sheaf/Holomorphic.lean), `TopCat.Sheaf.exact_of_exists_local_preimage` only; generalized from abelian-group sheaves to fixed-ring module sheaves |
| `HodgeConjecture/Geometry/EtaleAnalyticCoordinates.lean` | [Weil/AlgebraicGeometry/ComplexPoints/EtaleLocalHomeomorph.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/EtaleLocalHomeomorph.lean), local implicit-function and étale-chart proofs only; strengthened to complex analytic regularity; finite-type/Nullstellensatz and étale-site consequences omitted |
| `HodgeConjecture/Geometry/PolynomialComplexPoints.lean` | [Weil/AlgebraicGeometry/ComplexPoints/RiemannSurface.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/RiemannSurface.lean), polynomial-coordinate presentation argument; generalized to every finite dimension and reusing the existing affine structure map |
| `HodgeConjecture/Geometry/SmoothComplexManifold.lean` | [Weil/AlgebraicGeometry/ComplexPoints/RiemannSurface.lean](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/RiemannSurface.lean), algebraic atlas, regular-function and scheme-map proofs; generalized from curves to fixed relative dimension d using the strengthened analytic étale construction |

Upstream lists the Apache-2.0 license, reproduced in [LICENSE](LICENSE).
This directory contains attribution and license text, not a vendored copy of
Weil. Weil is a proof source here, not a Lake dependency.
