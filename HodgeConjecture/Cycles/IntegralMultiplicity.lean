import HodgeConjecture.Cycles.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Length

/-!
# Generic multiplicity of an integral closed subscheme

The generic stalk of an integral closed subscheme has length one as a module
over the ambient stalk, with scalars supplied by the actual closed-immersion
stalk map. This is the local length entering its fundamental-cycle coefficient,
not an assertion about an intersection product of cycles.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The generic multiplicity of an integral closed immersion is one, measured
over the ambient local ring through the actual stalk map. -/
theorem genericStalk_length_of_isClosedImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] :
    letI : Algebra (X.presheaf.stalk (i.base (genericPoint Z))) Z.functionField :=
      (i.stalkMap (genericPoint Z)).hom.toAlgebra
    Module.length (X.presheaf.stalk (i.base (genericPoint Z))) Z.functionField = 1 := by
  letI : Algebra (X.presheaf.stalk (i.base (genericPoint Z))) Z.functionField :=
    (i.stalkMap (genericPoint Z)).hom.toAlgebra
  have hsurj : Function.Surjective
      (algebraMap (X.presheaf.stalk (i.base (genericPoint Z))) Z.functionField) :=
    i.stalkMap_surjective (genericPoint Z)
  letI : IsSimpleModule (X.presheaf.stalk (i.base (genericPoint Z))) Z.functionField :=
    isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, by
      intro x hx y
      obtain ⟨r, hr⟩ := hsurj (y / x)
      refine ⟨r, ?_⟩
      change algebraMap _ _ r * x = y
      rw [hr, div_mul_cancel₀ y hx]⟩
  exact Module.length_eq_one _ _

/-- The ambient-stalk length of the existing actual integral cycle support. -/
theorem integralSubscheme_genericStalk_length {X : Scheme.{u}}
    (Z : IntegralClosedSubscheme X) :
    letI := Z.property
    letI : Algebra
        (X.presheaf.stalk (Z.val.subschemeι.base (genericPoint Z.val.subscheme)))
        Z.val.subscheme.functionField :=
      (Z.val.subschemeι.stalkMap (genericPoint Z.val.subscheme)).hom.toAlgebra
    Module.length
      (X.presheaf.stalk (Z.val.subschemeι.base (genericPoint Z.val.subscheme)))
      Z.val.subscheme.functionField = 1 := by
  letI := Z.property
  exact genericStalk_length_of_isClosedImmersion Z.val.subschemeι

end

end HodgeConjecture.SchemeCycles
