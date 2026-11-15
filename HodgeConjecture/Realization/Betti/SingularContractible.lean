module

public import HodgeConjecture.Realization.Betti.SingularHomotopy
public import HodgeConjecture.Realization.Betti.SingularPathConnected
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

/-!
# Actual singular cohomology of contractible spaces

The positive-degree point calculation is the dual of the original native
singular-chain exactness theorem. A proved topological contraction then
gives vanishing of every positive rational singular cohomology group.
Degree zero retains the existing constant-cocycle evaluation coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularContractible

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- Positive-degree singular cohomology vanishes for every totally disconnected space,
using the actual native chain exactness and exact rational dualization. -/
theorem isZero_cohomology_of_totallyDisconnected (X : TopCat.{0}) [TotallyDisconnectedSpace X]
    (n : ℕ) (hn : n ≠ 0) : IsZero (SingularCochains.Cohomology X n) := by
  let K := SingularChainCoordinates.complex (TopCat.toSSet.obj X)
  have hK : K.ExactAt n :=
    AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℚ) n (ModuleCat.of ℚ ℚ) X hn
  have hD : (RationalDual.dualComplex K).ExactAt n :=
    RationalDual.map_exact (K.op.sc n) hK.op
  exact IsZero.of_iso hD.isZero_homology
    (homologyMapIso (CochainDualComparison.comparisonIso (TopCat.toSSet.obj X)) n).symm

/-- The actual positive-degree point cohomology is zero. -/
theorem isZero_point_cohomology (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularCochains.Cohomology (TopCat.of Unit) n) :=
  isZero_cohomology_of_totallyDisconnected _ n hn

/-- Every positive-degree cohomology group of an actual contractible space vanishes. -/
theorem isZero_cohomology (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : IsZero (SingularCochains.Cohomology (TopCat.of X) n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact IsZero.of_iso (isZero_point_cohomology n hn)
    (SingularHomotopy.homotopyEquivIso e n).symm

/-- An elementwise version of contractible positive-degree vanishing. -/
theorem cohomology_eq_zero (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) (z : SingularCochains.Cohomology (TopCat.of X) n) : z = 0 :=
  (ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology X n hn)).elim z 0

/-- The established vanishing theorem supplies actual positive-degree primitives. -/
theorem exists_primitive (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (z : SingularCochains.Cochain (TopCat.of X) (n + 1))
    (hz : SingularCochains.differential (TopCat.of X) (n + 1) z = 0) :
    ∃ b : SingularCochains.Cochain (TopCat.of X) n,
      SingularCochains.differential (TopCat.of X) n b = z := by
  let a : SingularCochains.Cocycle (TopCat.of X) (n + 1) := ⟨z, hz⟩
  have ha := (SingularCochains.cohomologyClass_eq_zero_iff (TopCat.of X) (n + 1) a).mp
    (cohomology_eq_zero X (n + 1) (by omega) (SingularCochains.cohomologyClass _ _ a))
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, congrArg Subtype.val hb⟩

/-- Evaluation at an original point identifies H⁰ of a contractible space with the rationals. -/
def cohomologyZeroEquiv (X : Type) [TopologicalSpace X] [ContractibleSpace X] (x : X) :
    SingularCochains.Cohomology (TopCat.of X) 0 ≃ₗ[ℚ] ℚ :=
  (SingularCochains.cohomologyZeroIso X).toLinearEquiv.trans
    (SingularDegreeZero.equivConstants X x).toLinearEquiv

end HodgeConjecture.SingularContractible
