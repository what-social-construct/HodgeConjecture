module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberSupportedClass
public import HodgeConjecture.Cycles.ProjectiveLineProductFiberCodimension

/-!
# Chow and supported Betti data for the two zero fibers

Each certificate identifies one actual integral codimension-one carrier with
the scheme-theoretic inverse image of the reduced zero point, records its
ordinary integral and rational Chow classes, and constructs its supported
Betti class by pulling back the point Thom class. The support and forgetting
equalities are proved. No map from the product Chow group to Betti cohomology
is constructed here; compatibility of such a map with these certificates is
a separate theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductFiberChowBettiData

open AlgebraicGeometry CategoryTheory HomologicalComplex
open HodgeConjecture.SchemeCycles
open HodgeConjecture.ProjectiveLineProductBetti
open HodgeConjecture.ProjectiveLineProductFiberSupportedClass
open HodgeConjecture.ProjectiveLineProductFibers

abbrev ProductSpace : TopCat := ProjectiveLineProductFiberSupportedClass.ProductSpace
abbrev δ := ProjectiveLineProductChow.dimensionFunction ℂ
abbrev IntegralChow := ChowGroup δ 1
abbrev RationalChow := RationalChowGroup δ 1

/-- The actual analytic map induced by a product-to-line scheme morphism,
expressed in the original projective-line point model. -/
def analyticProjection
    (π : projectiveLineProduct ℂ ⟶ projectiveLine ℂ)
    (hπ : π ≫ lineStructure = projectiveLineProductStructureMorphism ℂ) :
    ProductSpace ⟶ ProjectiveLinePointGysin.space :=
  SchemeBetti.map π hπ ≫ lineComparison

abbrev fiberComplement
    (π : projectiveLineProduct ℂ ⟶ projectiveLine ℂ)
    (hπ : π ≫ lineStructure = projectiveLineProductStructureMorphism ℂ) :=
  ProjectiveLinePointGysin.complementSubcomplex.preimage
    (TopCat.toSSet.map (analyticProjection π hπ))

/-- Pullback of the original oriented point Thom class in relative singular
cohomology, before forgetting support. -/
def pulledThom
    (π : projectiveLineProduct ℂ ⟶ projectiveLine ℂ)
    (hπ : π ≫ lineStructure = projectiveLineProductStructureMorphism ℂ) :
    RelativeCochains.Cohomology (fiberComplement π hπ) 2 :=
  homologyMap (RelativeCochains.pullback
    (TopCat.toSSet.map (analyticProjection π hπ)) le_rfl) 2
      ProjectiveLinePointGysin.supportedThomClass

/-- Bounded source and target certificate for an actual coordinate fiber.
The source class and supported target class are tied to the same closed
carrier; a Chow-to-Betti cycle-class law is not asserted. -/
structure FiberData
    (π : projectiveLineProduct ℂ ⟶ projectiveLine ℂ)
    (hπ : π ≫ lineStructure = projectiveLineProductStructureMorphism ℂ)
    (W : IntegralClosedSubscheme (projectiveLineProduct ℂ))
    (c : cyclesOfDegree ℤ δ 1)
    (q : IntegralChow)
    (r : RationalChow)
    (b : ProductH2) : Prop where
  carrier_eq_comap :
    W.val = ((pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)).val).comap π
  codimension_one : supportCodimension W = 1
  cycle_eq_fundamental : c.val = fundamentalCycle ℤ W
  integral_chow_eq : q = classMap δ 1 c
  rational_chow_eq : r = rationalClassMap δ 1 (cyclesOfDegreeRationalize δ 1 c)
  complement_eq_outside_carrier :
    fiberComplement π hπ = SingularSubcomplexes.subsetSingular ProductSpace
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉ W.val.support}
  betti_eq_forget_thom :
    b = RelativeCochains.forget (fiberComplement π hπ) 2 (pulledThom π hπ)

/-- The first coordinate zero fiber has an actual codimension-one Chow
class and a supported Betti realization that forgets to `firstClass`. -/
theorem firstFiberData :
    FiberData (projectiveLineProductFst ℂ)
      (projectiveLineProductFst_comp_structureMorphism ℂ)
      (projectiveLineProductZeroFirstCarrier ℂ)
      (ProjectiveLineProductChow.firstZeroCycle ℂ)
      (ProjectiveLineProductChow.firstZeroChowClass ℂ)
      (ProjectiveLineProductChow.firstZeroRationalChowClass ℂ) firstClass := by
  refine ⟨?_, ProjectiveLineProductFiberCodimension.firstZeroCarrier_codimension_one ℂ,
    rfl, rfl, ?_, ?_, ?_⟩
  · exact ProjectiveLineProductFiberClassInputs.firstCarrier_ideal_eq_comap_zeroPoint
  · simpa only [ProjectiveLineProductChow.firstZeroRationalChowClass,
      ProjectiveLineProductChow.firstZeroChowClass] using
      chowRationalize_classMap δ 1 (ProjectiveLineProductChow.firstZeroCycle ℂ)
  · change firstComplement = SingularSubcomplexes.subsetSingular ProductSpace
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉
          (projectiveLineProductZeroFirstCarrier ℂ).val.support}
    have hcarrier : (projectiveLineProductZeroFirstCarrier ℂ).val =
        firstFiberIdeal ℂ (projectiveLineZero ℂ) := by
      rw [projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal]
      simp only [zeroSectionPoint_eq_projectiveLineZero]
    simpa only [hcarrier] using firstComplement_eq_outside_fiber
  · change firstClass = RelativeCochains.forget firstComplement 2 firstSupportedClass
    exact forget_firstSupportedClass.symm

/-- The second coordinate zero fiber has the analogous actual data. -/
theorem secondFiberData :
    FiberData (projectiveLineProductSnd ℂ)
      (projectiveLineProductSnd_comp_structureMorphism ℂ)
      (projectiveLineProductZeroSecondCarrier ℂ)
      (ProjectiveLineProductChow.secondZeroCycle ℂ)
      (ProjectiveLineProductChow.secondZeroChowClass ℂ)
      (ProjectiveLineProductChow.secondZeroRationalChowClass ℂ) secondClass := by
  refine ⟨?_, ProjectiveLineProductFiberCodimension.secondZeroCarrier_codimension_one ℂ,
    rfl, rfl, ?_, ?_, ?_⟩
  · exact ProjectiveLineProductFiberClassInputs.secondCarrier_ideal_eq_comap_zeroPoint
  · simpa only [ProjectiveLineProductChow.secondZeroRationalChowClass,
      ProjectiveLineProductChow.secondZeroChowClass] using
      chowRationalize_classMap δ 1 (ProjectiveLineProductChow.secondZeroCycle ℂ)
  · change secondComplement = SingularSubcomplexes.subsetSingular ProductSpace
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉
          (projectiveLineProductZeroSecondCarrier ℂ).val.support}
    have hcarrier : (projectiveLineProductZeroSecondCarrier ℂ).val =
        secondFiberIdeal ℂ (projectiveLineZero ℂ) := by
      rw [projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal]
      simp only [zeroSectionPoint_eq_projectiveLineZero]
    simpa only [hcarrier] using secondComplement_eq_outside_fiber
  · change secondClass = RelativeCochains.forget secondComplement 2 secondSupportedClass
    exact forget_secondSupportedClass.symm

end HodgeConjecture.ProjectiveLineProductFiberChowBettiData

end
