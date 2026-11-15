module

public import HodgeConjecture.Realization.Betti.SingularSheafAcyclicity
public import HodgeConjecture.SheafCohomology.FlasqueHypercohomology

@[expose] public section

/-!
# The original singular sheaf complex computes its derived sections

The original nonnegative complex, extension by zero, module-valued
global-sections functor and derived-functor unit are retained.
Flasqueness is proved from the original topology hypotheses.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace HodgeConjecture.SingularCochains

variable (X : TopCat.{0})

attribute [local instance] HasDerivedCategory.standard

/-- The original whole-complex comparison is invertible whenever its native terms are flasque. -/
theorem derivedComparison_isIso_of_flasqueTerms (hX : ∀ q, (cochainSheaf X q).IsFlasque) :
    IsIso (SheafHypercohomology.comparison ℚ X (sheafComplex X)) :=
  SheafHypercohomology.comparison_isIso_of_flasqueTerms ℚ X (sheafComplex X) hX

/-- The proved all-open paracompactness criterion discharges the whole-complex comparison. -/
theorem derivedComparison_isIso_of_open_paracompact [T2Space X]
    (hpara : ∀ U : Opens X, ParacompactSpace U) :
    IsIso (SheafHypercohomology.comparison ℚ X (sheafComplex X)) :=
  derivedComparison_isIso_of_flasqueTerms X (cochainSheaf_isFlasque X hpara)

/-- Canonical locally compact second-countable Hausdorff point spaces satisfy the criterion. -/
theorem derivedComparison_isIso [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] :
    IsIso (SheafHypercohomology.comparison ℚ X (sheafComplex X)) :=
  derivedComparison_isIso_of_flasqueTerms X
    (cochainSheaf_isFlasque_of_locallyCompact_secondCountable X)

/-- The same comparison induces an isomorphism in every integer degree. -/
theorem derivedComparisonFromComplexHomology_isIso
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (n : ℤ) :
    IsIso (SheafHypercohomology.comparisonFromComplexHomology ℚ X (sheafComplex X) n) :=
  SheafHypercohomology.comparisonFromComplexHomology_isIso_of_flasqueTerms ℚ X
    (sheafComplex X) (cochainSheaf_isFlasque_of_locallyCompact_secondCountable X) n

/-- Homology of the existing termwise sections identifies the actual derived target. -/
def sheafSectionsHomologyIsoHypercohomology
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (n : ℤ) :
    (SheafHypercohomology.underivedGlobalSections ℚ X (sheafComplex X)).obj.homology n ≅
      SheafHypercohomology.hypercohomology ℚ X (sheafComplex X) n := by
  have := derivedComparisonFromComplexHomology_isIso X n
  exact asIso (SheafHypercohomology.comparisonFromComplexHomology ℚ X (sheafComplex X) n)

@[simp]
theorem sheafSectionsHomologyIsoHypercohomology_hom
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (n : ℤ) :
    (sheafSectionsHomologyIsoHypercohomology X n).hom =
      SheafHypercohomology.comparisonFromComplexHomology ℚ X (sheafComplex X) n := rfl

end HodgeConjecture.SingularCochains
