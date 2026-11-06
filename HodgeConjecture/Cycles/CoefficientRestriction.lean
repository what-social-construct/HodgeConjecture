module

public import HodgeConjecture.Cycles.CoefficientExtension
public import HodgeConjecture.Cycles.OpenGrading

@[expose] public section

/-!
# Coefficient extension and actual open restriction

The existing open restriction commutes with coefficientwise extension
from integers to rationals, on finite cycles and their homogeneous
submodules. The proof uses the actual reduced-closure coefficient formula;
it needs no finiteness or integrality assumption on the ambient schemes.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Actual open restriction commutes with coefficient extension on the
same integral closed supports. -/
theorem openRestriction_rationalize {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (c : Cycles X ℤ) :
    openRestriction ℚ j
        (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c) =
      Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _)
        (openRestriction ℤ j c) := by
  ext W
  simp only [openRestriction_apply, Finsupp.mapRange_apply]

/-- The same coefficient comparison holds in the existing homogeneous
submodules for the actual restricted dimension function. -/
theorem gradedOpenRestriction_rationalize {U X : Scheme.{u}}
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (c : cyclesOfDegree ℤ δ n) :
    gradedOpenRestriction ℚ δ j n (cyclesOfDegreeRationalize δ n c) =
      cyclesOfDegreeRationalize (δ.comapOpenImmersion j) n
        (gradedOpenRestriction ℤ δ j n c) := by
  apply Subtype.ext
  exact openRestriction_rationalize j c.val

end

end HodgeConjecture.SchemeCycles
