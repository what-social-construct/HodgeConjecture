module

public import HodgeConjecture.Boundary.Normalization.NormalClosureConstruction
public import HodgeConjecture.Boundary.Normalization.SeparableFunctionField

@[expose] public section

/-!
# The marked normal closure of an actual function-field extension

The actual generic-stalk algebra of a finite dominant morphism of integral
schemes supplies the existing `NormalClosureData`, with normal closure inside
an algebraic closure of the upstairs function field. The marked embedding
retains the canonical copy of that upstairs field in its algebraic closure.

For a formally unramified morphism, the proved generic separability makes this
finite normal closure Galois. In particular finite étale morphisms qualify,
without any perfect-base-field or characteristic-zero assumption.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (p : Y ⟶ X) [IsDominant p] [IsFinite p]

/-- The existing marked normal-closure package, constructed from the actual
finite generic-stalk extension rather than supplied as a geometric input. -/
def functionFieldNormalClosureData :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    NormalClosureData X.functionField Y.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) := by
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Y.functionField :=
    functionFieldMapOfDominant_finiteDimensional p
  exact NormalClosureData.ofAlgebraicClosure X.functionField Y.functionField

/-- The constructed marking is the canonical upstairs embedding when viewed
in its ambient algebraic closure. -/
theorem functionFieldNormalClosureData_embedding_apply (x : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding x : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) x := by
  rfl

/-- Formal unramifiedness supplies separability for the constructed finite
normal closure of the actual generic extension, hence makes it Galois. -/
theorem functionFieldNormalClosure_isGalois [FormallyUnramified p] :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    IsGalois X.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) := by
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra.IsSeparable X.functionField Y.functionField :=
    functionFieldMapOfDominant_isSeparable p
  exact (functionFieldNormalClosureData p).isGalois_of_isSeparable

end

end HodgeConjecture.CollisionFoundations
