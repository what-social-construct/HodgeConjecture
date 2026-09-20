import HodgeConjecture.Boundary.Normalization.GluedNormalClosureRefinement
import HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedNormalClosure
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Finite étaleness of the original glued marked refinement

Finite cancellation through a separated morphism is proved by the graph
factorization. Applying it and étale cancellation to the existing marked
triangle gives finite étaleness of the original global refinement. No chart,
normalization carrier, or function-field marking is replaced.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles NormalizationInertia

noncomputable section

universe u

/-- A finite composite has finite first leg when its second leg is separated.
The second leg need not itself be finite. -/
theorem isFinite_of_comp_of_isSeparated {Z Y X : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsFinite (f ≫ g)] [IsSeparated g] :
    IsFinite f := by
  rw [← pullback.lift_snd (𝟙 _) f (Category.id_comp (f ≫ g))]
  have := MorphismProperty.pullback_snd (P := @IsFinite) (f ≫ g) g inferInstance
  infer_instance

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [IsEtale p]

/-- The original glued marked refinement is finite étale under the same
explicit normal-stalk inputs as the global normal-closure structural map. -/
theorem gluedNormalClosureToCover_finite_etale
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsFinite (gluedNormalClosureToCover p hY) ∧
      IsEtale (gluedNormalClosureToCover p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  have h := functionFieldNormalClosure_glued_finite_etale p hX hY
  haveI : IsFinite (gluedNormalClosureToCover p hY ≫ p) := by
    rw [gluedNormalClosureToCover_comp_toBase]
    exact h.1
  haveI : IsEtale (gluedNormalClosureToCover p hY ≫ p) := by
    rw [gluedNormalClosureToCover_comp_toBase]
    exact h.2
  exact ⟨isFinite_of_comp_of_isSeparated (gluedNormalClosureToCover p hY) p,
    IsEtale.of_comp (gluedNormalClosureToCover p hY) p⟩

end

end HodgeConjecture.CollisionFoundations
