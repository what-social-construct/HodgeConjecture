import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Function fields through actual scheme isomorphisms

An isomorphism of integral schemes carries the generic point to the generic
point. Its actual map on that stalk therefore gives an isomorphism of
function fields, in the contravariant direction. Naturality of stalk maps
with respect to specialization proves compatibility with the canonical
maps from every local ring into its function field.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic-point stalk isomorphism, directed contravariantly. -/
def functionFieldIso (e : X ≅ Y) : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion e.hom).symm) ≪≫
    asIso (e.hom.stalkMap (genericPoint X))

/-- The function-field equivalence induced by the actual scheme isomorphism. -/
def functionFieldEquiv (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (functionFieldIso e).commRingCatIsoToRingEquiv

/-- The generic-point isomorphism commutes with the actual specialization
maps from local stalks. -/
theorem functionFieldIso_stalkSpecializes (e : X ≅ Y) (x : X) :
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes
        (Set.mem_univ (e.hom.base x))) ≫ (functionFieldIso e).hom =
      e.hom.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) := by
  unfold functionFieldIso
  simp only [Iso.trans_hom, TopCat.Presheaf.stalkCongr_hom, asIso_hom,
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact Scheme.stalkSpecializes_stalkMap e.hom (genericPoint X) x
    ((genericPoint_spec X).specializes (Set.mem_univ x))

/-- Compatibility with the canonical algebra maps from actual local rings
to function fields; the local map is the scheme isomorphism's stalk map. -/
theorem functionFieldEquiv_algebraMap (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom.base x)) :
    functionFieldEquiv e
        (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((e.hom.stalkMap x).hom a) := by
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (functionFieldIso_stalkSpecializes e x)) a

end

end HodgeConjecture.SchemeCycles
