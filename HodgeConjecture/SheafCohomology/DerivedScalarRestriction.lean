module

public import HodgeConjecture.SheafCohomology.ScalarRestriction
public import HodgeConjecture.SheafCohomology.FlasqueHypercohomology
public import HodgeConjecture.SheafCohomology.HypercohomologyComparison
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public noncomputable section

/-!
# Actual derived sections under scalar restriction

The same injective resolution in the larger coefficient category is
restricted termwise. Its restricted terms are flasque, so the existing
whole-complex comparison computes derived sections without assuming
that scalar restriction preserves injective sheaves.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HodgeConjecture.SheafCohomology.ScalarRestriction

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- Ordinary derived sections commute with native scalar restriction, through one actual resolution. -/
def cohomologyIso (F : TopCat.Sheaf (ModuleCat.{u} S) X) (n : ℕ) :
    ((SheafHypercohomology.globalSections R X).rightDerived n).obj ((sheaves f X).obj F) ≅
      (ModuleCat.restrictScalars f).obj
        (((SheafHypercohomology.globalSections S X).rightDerived n).obj F) := by
  let T := sheaves f X
  let I := injectiveResolution F
  let K := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).app F
  let i : (CochainComplex.single₀ _).obj (T.obj F) ⟶ K :=
    e.inv ≫ (T.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso i := by dsimp [i]; infer_instance
  have hK (q : ℕ) : (K.X q).IsFlasque := injective_isFlasque f X (I.cocomplex.X q)
  exact (SheafHypercohomology.singleIsoRightDerived R X (T.obj F) n).symm ≪≫
    SheafHypercohomology.hypercohomologyIsoOfQuasiIso R X i (n : ℤ) ≪≫
    (SheafHypercohomology.complexHomologyIsoHypercohomology R X K hK (n : ℤ)).symm ≪≫
    (SheafHypercohomology.nonnegativeSectionsHomologyIso R X K n).symm ≪≫
    (I.isoRightDerivedObj ((SheafHypercohomology.globalSections S X) ⋙
      ModuleCat.restrictScalars f) n).symm ≪≫
    (BoundedBelowDerived.rightDerivedPostcomposeIso (SheafHypercohomology.globalSections S X)
      (ModuleCat.restrictScalars f) F n).symm

/-- Coefficient change on the original constant sheaf, with the actual ordinary derived target. -/
def constantCohomologyMap (n : ℕ) :
    ((SheafHypercohomology.globalSections R X).rightDerived n).obj (ConstantLift.sheaf R X) ⟶
      (ModuleCat.restrictScalars f).obj
        (((SheafHypercohomology.globalSections S X).rightDerived n).obj (ConstantLift.sheaf S X)) :=
  ((SheafHypercohomology.globalSections R X).rightDerived n).map (constantMap f X) ≫
    (cohomologyIso f X (ConstantLift.sheaf S X) n).hom

/-- An injective map from a field splits linearly on coefficients, hence on native constant sheaves. -/
theorem constantMap_isSplitMono {K A : Type u} [Field K] [CommRing A]
    (g : K →+* A) (hg : Function.Injective g) (Y : TopCat.{u}) :
    IsSplitMono (constantMap g Y) := by
  have hinj : Function.Injective (coefficientModuleMap g).hom := hg
  obtain ⟨r, hr⟩ := (coefficientModuleMap g).hom.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have : IsSplitMono (coefficientModuleMap g) := ⟨⟨{
    retraction := ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars g).obj (ModuleCat.of A A)) (Y := ModuleCat.of K K) r
    id := by
      apply ModuleCat.hom_ext
      exact hr }⟩⟩
  unfold constantMap
  infer_instance

/-- Splitting is preserved by the actual ordinary derived functor, without a finiteness assumption. -/
theorem constantCohomologyMap_mono (n : ℕ) [IsSplitMono (constantMap f X)] :
    Mono (constantCohomologyMap f X n) := by
  unfold constantCohomologyMap
  infer_instance

end HodgeConjecture.SheafCohomology.ScalarRestriction
