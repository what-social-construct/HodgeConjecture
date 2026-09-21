import HodgeConjecture.Cycles.FunctionFieldMap
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Extensionality from actual function-field pullbacks

The generic-stalk pullback of a dominant morphism gives its actual restriction
to the generic-point spectrum. Relative separatedness then makes this pullback
determine a dominant morphism between integral schemes over a fixed base.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual function-field map describes restriction to the generic point. -/
theorem functionFieldMapOfDominant_fromSpecStalk (f : X ⟶ Y) [IsDominant f] :
    Spec.map (functionFieldMapOfDominant f) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  simp only [functionFieldMapOfDominant, TopCat.Presheaf.stalkCongr_hom,
    Spec.map_comp, Category.assoc, Scheme.Spec_map_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_map_stalkMap_fromSpecStalk]

private theorem isDominant_fromSpecGenericPoint :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec X).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)),
      Scheme.fromSpecStalk_closedPoint⟩

/-- Dominant maps into a relatively separated scheme are determined by their
actual function-field pullbacks once their composites to the base agree. -/
theorem eq_of_functionFieldMapOfDominant_eq
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g]
    (s : Y ⟶ S) [IsSeparated s] (hbase : f ≫ s = g ≫ s)
    (hfield : functionFieldMapOfDominant f = functionFieldMapOfDominant g) :
    f = g := by
  letI := isDominant_fromSpecGenericPoint (X := X)
  apply ext_of_isDominant_of_isSeparated s hbase
    (X.fromSpecStalk (genericPoint X))
  rw [← functionFieldMapOfDominant_fromSpecStalk f,
    ← functionFieldMapOfDominant_fromSpecStalk g, hfield]

end

end HodgeConjecture.SchemeCycles
