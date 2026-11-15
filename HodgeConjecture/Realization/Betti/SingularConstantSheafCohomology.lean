module

public import HodgeConjecture.Realization.Betti.SingularSheafGlobalSections
public import HodgeConjecture.Realization.Betti.SingularSheafHypercohomology
public import HodgeConjecture.Realization.Betti.SingularSheafResolution
public import HodgeConjecture.SheafCohomology.HypercohomologyComparison

@[expose] public noncomputable section

/-!
# Original rational singular cohomology and derived constant-sheaf cohomology

The comparison composes the original global unit, the existing whole-complex
derived comparison, and the inverse of the original local constant-sheaf
resolution. The target is the ordinary right derived functor of the same
module-valued global-sections functor on the same rational constant sheaf.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HodgeConjecture.SingularCochains

variable (X : TopCat.{0})

attribute [local instance] HasDerivedCategory.standard

/-- The original global-unit map followed by the original derived comparison. -/
def cohomologyToHypercohomology (n : ℕ) :
    Cohomology X n ⟶ SheafHypercohomology.hypercohomology ℚ X (sheafComplex X) (n : ℤ) :=
  homologyMap (globalCochainsToSheaf X) n ≫
    (SheafHypercohomology.nonnegativeSectionsHomologyIso ℚ X (sheafComplex X) n).hom ≫
    SheafHypercohomology.comparisonFromComplexHomology ℚ X (sheafComplex X) (n : ℤ)

/-- The global unit and whole-complex comparison retain their separately proved hypotheses. -/
theorem cohomologyToHypercohomology_isIso_of_flasqueTerms [ParacompactSpace X] [T2Space X]
    (hX : ∀ q, (cochainSheaf X q).IsFlasque) (n : ℕ) :
    IsIso (cohomologyToHypercohomology X n) := by
  have : QuasiIso (globalCochainsToSheaf X) := globalCochainsToSheaf_quasiIso X
  have := SheafHypercohomology.comparisonFromComplexHomology_isIso_of_flasqueTerms ℚ X
    (sheafComplex X) hX (n : ℤ)
  unfold cohomologyToHypercohomology
  infer_instance

/-- The already proved topology criterion discharges both global comparison steps. -/
theorem cohomologyToHypercohomology_isIso [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (n : ℕ) : IsIso (cohomologyToHypercohomology X n) :=
  cohomologyToHypercohomology_isIso_of_flasqueTerms X
    (cochainSheaf_isFlasque_of_locallyCompact_secondCountable X) n

/-- The original local resolution induces this isomorphism on the existing derived target. -/
def constantResolutionHypercohomologyIso [StronglyLocallyContractibleSpace X] (n : ℤ) :
    SheafHypercohomology.hypercohomology ℚ X
        ((CochainComplex.single₀ _).obj (constantSheaf X)) n ≅
      SheafHypercohomology.hypercohomology ℚ X (sheafComplex X) n := by
  have : QuasiIso (comparison X) := comparison_quasiIso X
  exact SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℚ X (comparison X) n

@[simp]
theorem constantResolutionHypercohomologyIso_hom [StronglyLocallyContractibleSpace X] (n : ℤ) :
    (constantResolutionHypercohomologyIso X n).hom =
      SheafHypercohomology.hypercohomologyMap ℚ X (comparison X) n := rfl

/-- The actual comparison to ordinary right-derived sections of the original constant sheaf. -/
def cohomologyToConstantSheafDerived [StronglyLocallyContractibleSpace X] (n : ℕ) :
    Cohomology X n ⟶
      ((SheafHypercohomology.globalSections ℚ X).rightDerived n).obj (constantSheaf X) :=
  cohomologyToHypercohomology X n ≫ (constantResolutionHypercohomologyIso X (n : ℤ)).inv ≫
    (SheafHypercohomology.singleIsoRightDerived ℚ X (constantSheaf X) n).hom

/-- Original point-topology hypotheses prove invertibility; no comparison is supplied. -/
theorem cohomologyToConstantSheafDerived_isIso [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    IsIso (cohomologyToConstantSheafDerived X n) := by
  have := cohomologyToHypercohomology_isIso X n
  unfold cohomologyToConstantSheafDerived
  infer_instance

/-- Rational singular cohomology identifies the existing derived cohomology of the constant sheaf. -/
def cohomologyIsoConstantSheafDerived [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    Cohomology X n ≅
      ((SheafHypercohomology.globalSections ℚ X).rightDerived n).obj (constantSheaf X) := by
  have := cohomologyToConstantSheafDerived_isIso X n
  exact asIso (cohomologyToConstantSheafDerived X n)

@[simp]
theorem cohomologyIsoConstantSheafDerived_hom [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    (cohomologyIsoConstantSheafDerived X n).hom = cohomologyToConstantSheafDerived X n := rfl

/-- The composite commutes with the original resolution map and single-sheaf identification. -/
@[reassoc]
theorem cohomologyToConstantSheafDerived_resolution [StronglyLocallyContractibleSpace X] (n : ℕ) :
    cohomologyToConstantSheafDerived X n ≫
        (SheafHypercohomology.singleIsoRightDerived ℚ X (constantSheaf X) n).inv ≫
        SheafHypercohomology.hypercohomologyMap ℚ X (comparison X) (n : ℤ) =
      cohomologyToHypercohomology X n := by
  rw [← constantResolutionHypercohomologyIso_hom]
  simp only [cohomologyToConstantSheafDerived, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- A class is zero in the derived constant-sheaf target exactly when it was zero originally. -/
theorem cohomologyToConstantSheafDerived_eq_zero_iff [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X]
    (n : ℕ) (α : Cohomology X n) : cohomologyToConstantSheafDerived X n α = 0 ↔ α = 0 := by
  have := cohomologyToConstantSheafDerived_isIso X n
  have hinj := (ModuleCat.mono_iff_injective (cohomologyToConstantSheafDerived X n)).mp inferInstance
  constructor
  · intro h
    apply hinj
    simpa using h
  · intro h
    simp [h]

end HodgeConjecture.SingularCochains
