import HodgeConjecture.Boundary.Normalization.GluedNormalizationProperties
import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosure

/-!
# Finite étaleness of the actual glued normal-closure map

The already constructed marked function-field normal closure is retained.
Its original chart maps are finite étale by the integral-selector construction;
the proved inverse-image comparisons transfer these properties to the global
map. Normal stalks remain explicit geometric hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles NormalizationInertia

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [IsEtale p]

/-- The original glued normal-closure map is finite étale under the same
explicit normal-stalk inputs as its constructed affine chart maps. -/
theorem functionFieldNormalClosure_glued_finite_etale
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    IsFinite (gluedNormalizationToBase X N) ∧
      IsEtale (gluedNormalizationToBase X N) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  have hcharts (U : NonemptyAffineChart X) :
      letI : Algebra Γ(X, U.val) N :=
        ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
      IsFinite (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) ∧
        IsEtale (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) := by
    exact finiteEtaleAffineNormalClosureToChart_finite_etale p U.val U.property.1
      (fun x => hX x.val) (fun y => hY y.val)
  exact ⟨(gluedNormalizationToBase_isFinite_iff X N).mpr (fun U => (hcharts U).1),
    (gluedNormalizationToBase_isEtale_iff X N).mpr (fun U => (hcharts U).2)⟩

end

end HodgeConjecture.CollisionFoundations
