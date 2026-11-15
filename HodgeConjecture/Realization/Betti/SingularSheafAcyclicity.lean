module

public import HodgeConjecture.Realization.Betti.SingularOpenRestriction
public import HodgeConjecture.SheafCohomology.FlasqueDerived

@[expose] public section

/-!
# Actual higher derived sections of the existing singular cochain sheaves

The native flasqueness proof discharges the shared derived-vanishing
theorem. This is vanishing for each individual sheaf term; the
cohomology of the whole singular complex is retained.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable (X : TopCat.{0})

/-- The existing flasque terms have no positive derived sections on any original open. -/
theorem isZero_cochainSheaf_cohomology_of_open_paracompact [T2Space X]
    (hpara : ∀ U : Opens X, ParacompactSpace U) (q : ℕ) (U : Opens X)
    (n : ℕ) (hn : 0 < n) :
    IsZero (SheafCohomology.TwoOpenModules.Hobj ℚ (𝟭 _) U n (cochainSheaf X q)) := by
  let : (cochainSheaf X q).IsFlasque := cochainSheaf_isFlasque X hpara q
  exact SheafCohomology.LinearCoefficients.isZero_cohomology_of_isFlasque ℚ X
    (cochainSheaf X q) U n hn

/-- Canonical locally compact second-countable Hausdorff examples satisfy the hypotheses. -/
theorem isZero_cochainSheaf_cohomology [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (q : ℕ) (U : Opens X) (n : ℕ) (hn : 0 < n) :
    IsZero (SheafCohomology.TwoOpenModules.Hobj ℚ (𝟭 _) U n (cochainSheaf X q)) := by
  let : (cochainSheaf X q).IsFlasque := cochainSheaf_isFlasque_of_locallyCompact_secondCountable X q
  exact SheafCohomology.LinearCoefficients.isZero_cohomology_of_isFlasque ℚ X
    (cochainSheaf X q) U n hn

/-- The result also names the original global-sections functor directly. -/
theorem isZero_cochainSheaf_derivedGlobalSections [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (q n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections ℚ X).rightDerived n).obj (cochainSheaf X q)) := by
  let : (cochainSheaf X q).IsFlasque := cochainSheaf_isFlasque_of_locallyCompact_secondCountable X q
  exact SheafCohomology.LinearCoefficients.isZero_rightDerived_globalSections_of_isFlasque ℚ X
    (cochainSheaf X q) n hn

end HodgeConjecture.SingularCochains
