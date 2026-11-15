module

public import HodgeConjecture.Realization.Betti.ComplexSingularGlobalSections
public import HodgeConjecture.Realization.Betti.ComplexSingularOpenRestriction
public import HodgeConjecture.Realization.Betti.ComplexSingularResolution
public import HodgeConjecture.SheafCohomology.FlasqueHypercohomology
public import HodgeConjecture.SheafCohomology.HypercohomologyComparison

@[expose] public noncomputable section

/-!
# Complex singular cohomology and the derived constant sheaf

The source is the unrestricted complex-valued dual of the native rational
singular chains. The comparison uses its original global sheafification unit,
the whole-complex derived comparison, and the native complex constant-sheaf
resolution. The topology hypotheses below prove each map invertible.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

attribute [local instance] HasDerivedCategory.standard

/-- The original complex global unit followed by the whole-complex derived comparison. -/
def cohomologyToHypercohomology (n : ℕ) :
    ComplexCohomology X n ⟶ SheafHypercohomology.hypercohomology ℂ X (sheafComplex X) (n : ℤ) :=
  homologyMap (globalCochainsToSheaf X) n ≫
    (SheafHypercohomology.nonnegativeSectionsHomologyIso ℂ X (sheafComplex X) n).hom ≫
    SheafHypercohomology.comparisonFromComplexHomology ℂ X (sheafComplex X) (n : ℤ)

/-- The global-unit and derived-section comparisons use their separately proved hypotheses. -/
theorem cohomologyToHypercohomology_isIso_of_flasqueTerms [ParacompactSpace X] [T2Space X]
    (hX : ∀ q, (cochainSheaf X q).IsFlasque) (n : ℕ) :
    IsIso (cohomologyToHypercohomology X n) := by
  have : QuasiIso (globalCochainsToSheaf X) := globalCochainsToSheaf_quasiIso X
  have := SheafHypercohomology.comparisonFromComplexHomology_isIso_of_flasqueTerms ℂ X
    (sheafComplex X) hX (n : ℤ)
  unfold cohomologyToHypercohomology
  infer_instance

/-- Locally compact, second-countable Hausdorff point spaces satisfy both comparisons. -/
theorem cohomologyToHypercohomology_isIso [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (n : ℕ) : IsIso (cohomologyToHypercohomology X n) :=
  cohomologyToHypercohomology_isIso_of_flasqueTerms X
    (cochainSheaf_isFlasque_of_locallyCompact_secondCountable X) n

/-- The native complex local resolution induces an isomorphism on derived sections. -/
def constantResolutionHypercohomologyIso [StronglyLocallyContractibleSpace X] (n : ℤ) :
    SheafHypercohomology.hypercohomology ℂ X
        ((CochainComplex.single₀ _).obj (constantSheaf X)) n ≅
      SheafHypercohomology.hypercohomology ℂ X (sheafComplex X) n := by
  have : QuasiIso (comparison X) := comparison_quasiIso X
  exact SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℂ X (comparison X) n

@[simp]
theorem constantResolutionHypercohomologyIso_hom [StronglyLocallyContractibleSpace X] (n : ℤ) :
    (constantResolutionHypercohomologyIso X n).hom =
      SheafHypercohomology.hypercohomologyMap ℂ X (comparison X) n := rfl

/-- The actual complex singular map to derived sections of the original constant sheaf. -/
def cohomologyToConstantSheafDerived [StronglyLocallyContractibleSpace X] (n : ℕ) :
    ComplexCohomology X n ⟶
      ((SheafHypercohomology.globalSections ℂ X).rightDerived n).obj (constantSheaf X) :=
  cohomologyToHypercohomology X n ≫ (constantResolutionHypercohomologyIso X (n : ℤ)).inv ≫
    (SheafHypercohomology.singleIsoRightDerived ℂ X (constantSheaf X) n).hom

/-- The topology hypotheses prove that the constructed complex comparison is invertible. -/
theorem cohomologyToConstantSheafDerived_isIso [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    IsIso (cohomologyToConstantSheafDerived X n) := by
  have := cohomologyToHypercohomology_isIso X n
  unfold cohomologyToConstantSheafDerived
  infer_instance

/-- The same isomorphism as a native category isomorphism. -/
def cohomologyIsoConstantSheafDerived [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    ComplexCohomology X n ≅
      ((SheafHypercohomology.globalSections ℂ X).rightDerived n).obj (constantSheaf X) := by
  have := cohomologyToConstantSheafDerived_isIso X n
  exact asIso (cohomologyToConstantSheafDerived X n)

@[simp]
theorem cohomologyIsoConstantSheafDerived_hom [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    (cohomologyIsoConstantSheafDerived X n).hom = cohomologyToConstantSheafDerived X n := rfl

/-- The derived map is fixed by the original complex constant-sheaf resolution. -/
@[reassoc]
theorem cohomologyToConstantSheafDerived_resolution [StronglyLocallyContractibleSpace X] (n : ℕ) :
    cohomologyToConstantSheafDerived X n ≫
        (SheafHypercohomology.singleIsoRightDerived ℂ X (constantSheaf X) n).inv ≫
        SheafHypercohomology.hypercohomologyMap ℂ X (comparison X) (n : ℤ) =
      cohomologyToHypercohomology X n := by
  rw [← constantResolutionHypercohomologyIso_hom]
  simp only [cohomologyToConstantSheafDerived, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end HodgeConjecture.SingularCoefficientChange
