module

public import HodgeConjecture.Realization.Betti.SingularCoefficientGlobalUnit

@[expose] public noncomputable section

/-!
# Cohomology of the original coefficient map

The original map from rational singular cochains to unrestricted complex-valued
cochains induces a map on the native homology objects. Exact scalar
restriction identifies its codomain with the underlying rational module of
complex singular cohomology.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

/-- The homology of the restricted complex is the restriction of its homology. -/
def restrictedComplexHomologyIso (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).obj
        (complexCochains X)).homology n ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (ComplexCohomology X n) :=
  ((complexCochains X).sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap ℚ ℂ))

/-- The original coefficient inclusion on rational singular cohomology. -/
def coefficientCohomologyMap (n : ℕ) :
    SingularCochains.Cohomology X n ⟶
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (ComplexCohomology X n) :=
  homologyMap (coefficientMap X) n ≫ (restrictedComplexHomologyIso X n).hom

end HodgeConjecture.SingularCoefficientChange
