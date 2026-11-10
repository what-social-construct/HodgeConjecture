module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChart
public import HodgeConjecture.Realization.Betti.RelativeMayerVietoris

@[expose] public section

/-!
# The original normal-chart boundary carries the actual local Thom class

Naturality of the original relative short exact sequences compares the
complex-line Thom class with the actual finite-chart local boundary.
The actual overlap homeomorphism and radial map fix the punctured source
and orientation. No absolute projective-line generator is used to define
the local class or select this comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineNormalChart

open CategoryTheory HomologicalComplex
open ProjectiveLineAnalyticCover

/-- The original nested intersection comparison retains actual punctured chart pullback. -/
theorem punctured_cohomology_comparison_inv (n : ℕ) :
    (RelativeMayerVietoris.intersectionCohomologyIso first second n).hom ≫
        homologyMap (SubcomplexCochains.pullback puncturedSSetMap) n =
      (SingularMayerVietoris.intersectionCohomologyIso space finiteOpen reciprocalOpen n).hom ≫
        SingularCochains.cohomologyPullback (TopCat.ofHom puncturedChart) n ≫
          (ComplexPointThom.puncturedCohomologyIso n).inv := by
  apply (cancel_mono (ComplexPointThom.puncturedCohomologyIso n).hom).mp
  simpa only [RelativeMayerVietoris.intersectionCohomologyIso,
    homologyMapIso_hom, SingularMayerVietoris.pullbackIso,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    punctured_cohomology_comparison n

/-- Naturality of the actual local relative boundary under the original finite normal chart. -/
theorem localConnectingActual_normalClassIso_inv (n : ℕ) :
    RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen n ≫
        (normalClassIso (n + 1)).inv =
      SingularCochains.cohomologyPullback (TopCat.ofHom puncturedChart) n ≫
        (ComplexPointThom.puncturedCohomologyIso n).inv ≫
          RelativeCochains.connecting ComplexPointThom.puncturedSubcomplex n := by
  change (SingularMayerVietoris.intersectionCohomologyIso space finiteOpen reciprocalOpen n).inv ≫
    (RelativeMayerVietoris.intersectionCohomologyIso first second n).hom ≫
      (RelativeCochains.connecting localBoundary n ≫
        homologyMap (RelativeCochains.pullback finiteSSetIso.hom punctured_preimage.le) (n + 1)) = _
  rw [RelativeCochains.connecting_naturality]
  have h := congrArg
    (fun f ↦ (SingularMayerVietoris.intersectionCohomologyIso space finiteOpen reciprocalOpen n).inv ≫
      f ≫ RelativeCochains.connecting ComplexPointThom.puncturedSubcomplex n)
    (punctured_cohomology_comparison_inv n)
  simpa only [puncturedSSetMap, Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The original punctured finite coordinate intertwines actual radial normalization. -/
theorem overlap_radial_comp :
    TopCat.ofHom puncturedChart ≫
      TopCat.ofHom overlapCircleHomotopyEquiv.toFun =
        TopCat.ofHom PuncturedComplexCircle.radial := by
  apply TopCat.ext
  intro z
  change overlapCircleHomotopyEquiv.toFun (overlapHomeomorph z) =
    PuncturedComplexCircle.radial z
  exact overlapCircleHomotopyEquiv_finite z

/-- The actual positive overlap orientation class, using the original radial map. -/
def overlapOrientationClass :
    SingularCochains.Cohomology (TopCat.of ↥(finiteOpen ∩ reciprocalOpen)) 1 :=
  SingularCochains.cohomologyPullback (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1
    CircleCohomology.coverGenerator

/-- Pullback along the original punctured chart gives the original complex-line angular class. -/
theorem overlapOrientationClass_pullback :
    SingularCochains.cohomologyPullback (TopCat.ofHom puncturedChart) 1
        overlapOrientationClass =
      SingularCochains.cohomologyPullback (TopCat.ofHom PuncturedComplexCircle.radial) 1
        CircleCohomology.coverGenerator := by
  change (SingularCochains.cohomologyPullback (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1 ≫
    SingularCochains.cohomologyPullback (TopCat.ofHom puncturedChart) 1)
      CircleCohomology.coverGenerator = _
  rw [← SingularCochains.cohomologyPullback_comp, overlap_radial_comp]

/-- The actual finite normal chart carries the actual local Thom class to its original local boundary. -/
theorem normalClassIso_thomClass :
    (normalClassIso 2).hom ComplexPointThom.thomClass =
      RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
        (SingularCochains.cohomologyPullback (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1
          CircleCohomology.coverGenerator) := by
  apply (normalClassIso 2).symm.toLinearEquiv.injective
  change (normalClassIso 2).inv ((normalClassIso 2).hom ComplexPointThom.thomClass) =
    (normalClassIso 2).inv
      (RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
        overlapOrientationClass)
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id]
  change ComplexPointThom.thomClass = _
  have h := congrArg (fun f ↦ f overlapOrientationClass)
    (localConnectingActual_normalClassIso_inv 1)
  change (normalClassIso 2).inv
      (RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
        overlapOrientationClass) =
    ComplexPointThom.connecting
      (SingularCochains.cohomologyPullback (TopCat.ofHom puncturedChart) 1
        overlapOrientationClass) at h
  rw [overlapOrientationClass_pullback] at h
  exact h.symm

end HodgeConjecture.ProjectiveLineNormalChart
