# Axiom Stacks proof attribution

Source: <https://github.com/AxiomMath/Stacks>

Pinned revision: `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

The following proof adaptations use that revision. Source paths below are
relative to the upstream repository; each adapted file also records its source.

| Project files | Upstream sources |
| --- | --- |
| `CommutativeAlgebra/DeRham/{Differential,Complex}.lean` | `StacksFrontier/RingTheory/DeRham/{Basic,Complex}.lean` (actual differential, uniqueness, square-zero and cochain packaging; base change and quotient descent omitted) |
| `Cycles/FiberResidueField.lean` | `StacksFrontier/AlgebraicGeometry/F6Rank128/FiberResidueField.lean` |
| `CommutativeAlgebra/Multiplicity/HomologicalComplexAbelian.lean` | `StacksCore/Algebra/Homology/HomologicalComplexAbelian.lean` |
| `Multiplicity/{ModuleOrder,Multiplication,SupportLength,TwoPeriodic,RestrictedDivisors}.lean` | `StacksFrontier/AlgebraicGeometry/Chow/CalculationMultiplicities/{LocalOrder,Multiplication,SupportLength,TwoPeriodic,RestrictedDivisors}.lean` |
| `Multiplicity/Periodic{Defs,Additivity,Length}.lean` | `StacksFrontier/AlgebraicGeometry/Chow/PeriodicComplexesHerbrand/{Defs,Additivity,Length}.lean` |
| `Multiplicity/{PrimeFiltration,Support,FiniteSupport}.lean` | `StacksFrontier/RingTheory/{Length/Additivity,Support/Basic,Support/Finite}.lean` |
| `Multiplicity/MinimalPrimeColength.lean`, `Cycles/ComponentStalk.lean` | `StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/IntersectionInvertibleSheaf.lean` (selected length and component lemmas) |
| `CommutativeAlgebra/FlatLocalMultiplicity.lean`, `Cycles/EquidimensionalDivisorPoint.lean`, `Cycles/FlatComponentFunction.lean` | `StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDivisor.lean` (selected local calculations) |
| `Cycles/IdealComap.lean` | `StacksFrontier/AlgebraicGeometry/{Groupoids/IdealSheafComap,DivisorFlatPullback/Basic}.lean` (affine inverse-image formulas) |
| `Cycles/IdealStalk.lean` | `StacksFrontier/AlgebraicGeometry/{Divisors/FittingIdeals/Basic,Divisors/RegularImmersion/FlatAtDivisor,ResolutionsAndBounds/IdealSheafStalk,Chow/RationalEquivalence/FlatPullbackPrincipalDivisor}.lean` (selected stalk lemmas) |
| `Cycles/StalkBaseChange.lean`, `Cycles/PullbackStalk.lean` | `StacksFrontier/AlgebraicGeometry/{Pullback/StalkFromSpecStalk,Perfect/BaseChangeStalk}.lean` |
| `Cycles/FiberStalkKernel.lean` | `StacksFrontier/AlgebraicGeometry/Chow/RelativeCycles/ModuleSpecialization/StalkLengths.lean` (selected pullback and fiber kernel lemmas) |
| `Cycles/FlatComponents.lean` | `StacksFrontier/AlgebraicGeometry/Chow/{FlatPullback/InverseImageDimension,RationalEquivalence/FlatPullbackPrincipalDivisor}.lean` (dominance of components) |

`Multiplicity/` above abbreviates `HodgeConjecture/CommutativeAlgebra/Multiplicity/`;
the other project paths are relative to `HodgeConjecture/`.
The adaptations use this project's existing schemes, supports, residue-field
actions, and Lean 4.35 APIs. Unneeded generality and metadata-only attributes
have been omitted. The upstream library is released under Apache-2.0; its
license is preserved in [LICENSE](LICENSE).

The external library is a proof reference, not a Lake dependency. Its general
reuse assessment is recorded in
[`research/working/0019-axiom-stacks-reuse-audit.md`](../../research/working/0019-axiom-stacks-reuse-audit.md).
