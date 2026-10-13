import HodgeConjecture.Boundary.Normalization.FiniteFunctionField
import Mathlib.RingTheory.Norm.Defs

/-!
# The norm along an actual finite dominant morphism

Use the actual generic-stalk pullback as the field algebra and derive its
finite dimensionality from the finite morphism. This is the rational
function appearing in Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f]

/-- The field norm on units, using the original function-field pullback. -/
def functionFieldNorm [IsFinite f] : X.functionFieldˣ →* Y.functionFieldˣ := by
  letI : Algebra Y.functionField X.functionField := (functionFieldMapOfDominant f).hom.toAlgebra
  letI := CollisionFoundations.functionFieldMapOfDominant_finiteDimensional f
  exact Units.map (Algebra.norm Y.functionField)

/-- The norm uses exactly the algebra structure of the actual generic-stalk map. -/
theorem functionFieldNorm_eq [IsFinite f] (g : X.functionFieldˣ) :
    letI : Algebra Y.functionField X.functionField := (functionFieldMapOfDominant f).hom.toAlgebra
    functionFieldNorm f g = Units.map (Algebra.norm Y.functionField) g := rfl

end

end HodgeConjecture.SchemeCycles
