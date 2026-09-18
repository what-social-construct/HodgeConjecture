import HodgeConjecture.Cycles.FunctionFieldTransport
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Function fields of actual dominant morphisms

A dominant morphism between integral schemes preserves the generic point.
Its actual map on that stalk gives the contravariant function-field map.
The map commutes with germs of sections and specializes to the existing
open-immersion isomorphism; no chosen fraction-field replacement is used.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y Z : Scheme.{u}}

/-- Dominance makes the inverse image of every nonempty open nonempty. -/
theorem nonempty_preimage_of_isDominant (p : Y ⟶ X) [IsDominant p]
    (U : X.Opens) [Nonempty U] : Nonempty (p ⁻¹ᵁ U) := by
  obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open U.isOpen
    (by simpa using ‹Nonempty U›)
  exact ⟨⟨y, hy⟩⟩

/-- A dominant morphism sends the generic point to the generic point. -/
theorem genericPoint_eq_of_isDominant (p : Y ⟶ X) [IsDominant p]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    p.base (genericPoint Y) = genericPoint X := by
  apply ((genericPoint_spec X).eq _).symm
  simpa only [Set.image_univ, p.denseRange.closure_range] using
    (genericPoint_spec Y).image p.continuous

variable [IsIntegral X] [IsIntegral Y]

/-- The actual generic-stalk map of a dominant morphism. -/
def functionFieldMapOfDominant (p : Y ⟶ X) [IsDominant p] :
    X.functionField ⟶ Y.functionField :=
  (X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isDominant p).symm)).hom ≫
    p.stalkMap (genericPoint Y)

/-- The induced map is an embedding of the actual function fields. -/
theorem functionFieldMapOfDominant_injective (p : Y ⟶ X) [IsDominant p] :
    Function.Injective (functionFieldMapOfDominant p) :=
  (functionFieldMapOfDominant p).hom.injective

/-- Generic germs commute with the actual pullback of sections. -/
theorem functionFieldMapOfDominant_germ (p : Y ⟶ X) [IsDominant p]
    (U : X.Opens) [Nonempty U] :
    letI := nonempty_preimage_of_isDominant p U
    X.germToFunctionField U ≫ functionFieldMapOfDominant p =
      p.app U ≫ Y.germToFunctionField (p ⁻¹ᵁ U) := by
  letI := nonempty_preimage_of_isDominant p U
  unfold functionFieldMapOfDominant Scheme.germToFunctionField
  rw [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.stalkMap_germ p U (genericPoint Y) _

/-- On an open immersion, the generic map is the existing stalk isomorphism. -/
theorem functionFieldMapOfDominant_eq_openImmersion (p : Y ⟶ X)
    [IsDominant p] [IsOpenImmersion p] :
    functionFieldMapOfDominant p = (functionFieldIsoOfOpenImmersion p).hom := rfl

/-- The identity scheme morphism induces the identity function-field map. -/
@[simp]
theorem functionFieldMapOfDominant_id :
    functionFieldMapOfDominant (𝟙 X) = 𝟙 X.functionField := by
  simp [functionFieldMapOfDominant, TopCat.Presheaf.stalkCongr_hom]

/-- Actual scheme composition induces contravariant composition of field maps. -/
theorem functionFieldMapOfDominant_comp [IsIntegral Z]
    (p : Y ⟶ X) (q : Z ⟶ Y) [IsDominant p] [IsDominant q] :
    functionFieldMapOfDominant (q ≫ p) =
      functionFieldMapOfDominant p ≫ functionFieldMapOfDominant q := by
  simp only [functionFieldMapOfDominant, TopCat.Presheaf.stalkCongr_hom,
    Scheme.stalkMap_comp, Category.assoc]
  rw [← Scheme.stalkSpecializes_stalkMap_assoc,
    TopCat.Presheaf.stalkSpecializes_comp_assoc]


end

end HodgeConjecture.SchemeCycles
