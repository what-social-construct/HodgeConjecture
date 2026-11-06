module

public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

/-!
# Function fields through actual open immersions

An open immersion of integral schemes carries the generic point to the generic
point. Its actual map on that stalk therefore gives an isomorphism of
function fields, in the contravariant direction. Naturality of stalk maps
with respect to specialization proves compatibility with the canonical
maps from every local ring into its function field. The existing scheme
isomorphism APIs are specializations of this same construction.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic-point stalk isomorphism, directed contravariantly. -/
def functionFieldIsoOfOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] :
    Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint X))

/-- The function-field equivalence induced by the actual open immersion. -/
def functionFieldEquivOfOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] :
    Y.functionField ≃+* X.functionField :=
  (functionFieldIsoOfOpenImmersion j).commRingCatIsoToRingEquiv

/-- The generic-point isomorphism commutes with the actual specialization
maps from local stalks. -/
theorem functionFieldIsoOfOpenImmersion_stalkSpecializes
    (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes
        (Set.mem_univ (j.base x))) ≫ (functionFieldIsoOfOpenImmersion j).hom =
      j.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) := by
  unfold functionFieldIsoOfOpenImmersion
  simp only [Iso.trans_hom, TopCat.Presheaf.stalkCongr_hom, asIso_hom,
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap j (genericPoint X) x
    ((genericPoint_spec X).specializes (Set.mem_univ x))

/-- Compatibility with the canonical algebra maps from actual local rings
to function fields; the local map is the open immersion's actual stalk map. -/
theorem functionFieldEquivOfOpenImmersion_algebraMap
    (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (a : Y.presheaf.stalk (j.base x)) :
    functionFieldEquivOfOpenImmersion j
        (algebraMap (Y.presheaf.stalk (j.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((j.stalkMap x).hom a) := by
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (functionFieldIsoOfOpenImmersion_stalkSpecializes j x)) a

/-- The existing isomorphism API specializes the actual open-immersion map. -/
def functionFieldIso (e : X ≅ Y) : Y.functionField ≅ X.functionField :=
  functionFieldIsoOfOpenImmersion e.hom

/-- The same function-field equivalence for a scheme isomorphism. -/
def functionFieldEquiv (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  functionFieldEquivOfOpenImmersion e.hom

/-- Specialization compatibility for the scheme-isomorphism specialization. -/
theorem functionFieldIso_stalkSpecializes (e : X ≅ Y) (x : X) :
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes
        (Set.mem_univ (e.hom.base x))) ≫ (functionFieldIso e).hom =
      e.hom.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) :=
  functionFieldIsoOfOpenImmersion_stalkSpecializes e.hom x

/-- The old local-algebra comparison uses the same actual stalk map. -/
theorem functionFieldEquiv_algebraMap (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom.base x)) :
    functionFieldEquiv e
        (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((e.hom.stalkMap x).hom a) :=
  functionFieldEquivOfOpenImmersion_algebraMap e.hom x a

end

end HodgeConjecture.SchemeCycles
