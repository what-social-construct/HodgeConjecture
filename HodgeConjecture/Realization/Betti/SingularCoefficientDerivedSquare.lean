module

public import HodgeConjecture.Realization.Betti.SingularCoefficientCohomology
public import HodgeConjecture.Realization.Betti.SingularConstantSheafCohomology
public import HodgeConjecture.Realization.Betti.ComplexSingularConstantSheafCohomology
public import HodgeConjecture.SheafCohomology.DerivedScalarRestrictionNaturality

@[expose] public noncomputable section

/-!
# Coefficient change across the original singular resolutions

The rational and complex singular sheaf complexes carry the original
coefficient map. Scalar restriction computes the same sections term by
term, and the native flasque comparisons give a cross-coefficient
hypercohomology identification.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

abbrev res := ModuleCat.restrictScalars (algebraMap ℚ ℂ)
abbrev sheafRes := SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X
abbrev sectionsC := SheafHypercohomology.globalSections ℂ X
abbrev sectionsQ := SheafHypercohomology.globalSections ℚ X

/-- Native fixed-complex-module injective sheaves have surjective open restrictions. -/
theorem injectiveSheaf_isFlasque
    (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) [Injective F] : F.IsFlasque :=
  ⟨fun {_U _V} j => (ModuleCat.epi_iff_surjective _).mpr
    (SheafCohomology.Cohomology.LinearRestriction.injective_linear_restriction_surjective
      F (leOfHom j.unop))⟩

/-- Scalar restriction of termwise sections has the native restricted homology. -/
def restrictedSectionsHomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ) (n : ℕ) :
    (((sectionsQ X).mapHomologicalComplex (.up ℕ)).obj
      (((sheafRes X).mapHomologicalComplex (.up ℕ)).obj K)).homology n ≅
      (res).obj ((((sectionsC X).mapHomologicalComplex (.up ℕ)).obj K).homology n) :=
  ((((sectionsC X).mapHomologicalComplex (.up ℕ)).obj K).sc n).mapHomologyIso res

/-- The restricted-sections homology identification respects a map of complex sheaves. -/
@[reassoc]
theorem restrictedSectionsHomologyIso_hom_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ}
    (φ : K ⟶ L) (n : ℕ) :
    homologyMap
        (((sectionsQ X).mapHomologicalComplex (.up ℕ)).map
          (((sheafRes X).mapHomologicalComplex (.up ℕ)).map φ)) n ≫
      (restrictedSectionsHomologyIso X L n).hom =
    (restrictedSectionsHomologyIso X K n).hom ≫
      res.map (homologyMap (((sectionsC X).mapHomologicalComplex (.up ℕ)).map φ) n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{0} ℂ) (.up ℕ) n).map
      (((sectionsC X).mapHomologicalComplex (.up ℕ)).map φ)) res

/-- The literal coefficient map agrees with the two original global units on homology. -/
@[reassoc]
theorem coefficientCohomologyMap_sections (n : ℕ) :
    homologyMap (SingularCochains.globalCochainsToSheaf X) n ≫
        homologyMap
          (((sectionsQ X).mapHomologicalComplex (.up ℕ)).map (sheafCoefficientMap X)) n ≫
        (restrictedSectionsHomologyIso X (sheafComplex X) n).hom =
      coefficientCohomologyMap X n ≫
        res.map (homologyMap (globalCochainsToSheaf X) n) := by
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{0} ℂ) (.up ℕ) n).map (globalCochainsToSheaf X)) res
  change homologyMap ((res.mapHomologicalComplex (.up ℕ)).map (globalCochainsToSheaf X)) n ≫
      (restrictedSectionsHomologyIso X (sheafComplex X) n).hom =
    (restrictedComplexHomologyIso X n).hom ≫
      res.map (homologyMap (globalCochainsToSheaf X) n) at hnat
  calc
    _ = homologyMap (coefficientMap X) n ≫
          homologyMap ((res.mapHomologicalComplex (.up ℕ)).map (globalCochainsToSheaf X)) n ≫
          (restrictedSectionsHomologyIso X (sheafComplex X) n).hom := by
            exact congrArg (fun h => h ≫ (restrictedSectionsHomologyIso X (sheafComplex X) n).hom)
              (globalUnit_coefficient_homology X n)
    _ = homologyMap (coefficientMap X) n ≫ (restrictedComplexHomologyIso X n).hom ≫
          res.map (homologyMap (globalCochainsToSheaf X) n) := by
            simpa only [Category.assoc] using
              congrArg (fun h => homologyMap (coefficientMap X) n ≫ h) hnat
    _ = _ := by rfl

/-- The original flasque complexes compute compatible rational and complex hypercohomology. -/
def restrictedHypercohomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ)
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℕ) :
    SheafHypercohomology.hypercohomology ℚ X
      (((sheafRes X).mapHomologicalComplex (.up ℕ)).obj K) (n : ℤ) ≅
      res.obj (SheafHypercohomology.hypercohomology ℂ X K (n : ℤ)) := by
  let hTK (q : ℕ) :
      ((((sheafRes X).mapHomologicalComplex (.up ℕ)).obj K).X q).IsFlasque := by
    let : (K.X q).IsFlasque := hK q
    exact SheafCohomology.ScalarRestriction.isFlasque (algebraMap ℚ ℂ) X (K.X q)
  exact (SheafHypercohomology.complexHomologyIsoHypercohomology ℚ X
      (((sheafRes X).mapHomologicalComplex (.up ℕ)).obj K) hTK (n : ℤ)).symm ≪≫
    (SheafHypercohomology.nonnegativeSectionsHomologyIso ℚ X
      (((sheafRes X).mapHomologicalComplex (.up ℕ)).obj K) n).symm ≪≫
    restrictedSectionsHomologyIso X K n ≪≫
    res.mapIso (SheafHypercohomology.nonnegativeSectionsHomologyIso ℂ X K n) ≪≫
    res.mapIso (SheafHypercohomology.complexHomologyIsoHypercohomology ℂ X K hK (n : ℤ))

/-- Compute scalar restriction of derived sections through the same complex
injective resolution on both sides. This gives a concrete flasque-resolution
version of the native scalar-restriction isomorphism. -/
def restrictedCohomologyViaInjectiveIso
    (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) (n : ℕ) :
    ((sectionsQ X).rightDerived n).obj ((sheafRes X).obj F) ≅
      res.obj (((sectionsC X).rightDerived n).obj F) := by
  let I := injectiveResolution F
  let K := I.cocomplex
  let e := (HomologicalComplex.singleMapHomologicalComplex (sheafRes X) (.up ℕ) 0).app F
  let i : (CochainComplex.single₀ _).obj ((sheafRes X).obj F) ⟶
      ((sheafRes X).mapHomologicalComplex (.up ℕ)).obj K :=
    e.inv ≫ ((sheafRes X).mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso i := by dsimp [i]; infer_instance
  let hK (q : ℕ) : (K.X q).IsFlasque := by
    let : Injective (K.X q) := inferInstance
    exact injectiveSheaf_isFlasque X (K.X q)
  have : QuasiIso I.ι := inferInstance
  exact (SheafHypercohomology.singleIsoRightDerived ℚ X ((sheafRes X).obj F) n).symm ≪≫
    SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℚ X i (n : ℤ) ≪≫
    restrictedHypercohomologyIso X K hK n ≪≫
    res.mapIso (SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℂ X I.ι (n : ℤ)).symm ≪≫
    res.mapIso (SheafHypercohomology.singleIsoRightDerived ℂ X F n)

end HodgeConjecture.SingularCoefficientChange
