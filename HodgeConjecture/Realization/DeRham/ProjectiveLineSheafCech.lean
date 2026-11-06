module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineFormsSheaf
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCechReduction
public import HodgeConjecture.SheafCohomology.TwoOpenModules
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels

@[expose] public noncomputable section

/-!
# The original degree-two quotient and the actual one-form sheaf Čech cokernel

The coordinates below come from the proved canonical sheafification units
and actual chart restrictions. The overlap sign records the original
infinity-minus-zero convention. No rank-one coordinate identification is
used to choose this comparison.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open KaehlerDifferential

universe u

namespace HodgeConjecture.ProjectiveLineDeRham

variable (k : Type u) [Field k]

private theorem moduleBiprodCoordinates_apply (M N : ModuleCat.{u} k)
    (x : (M ⊞ N : ModuleCat.{u} k)) :
    (ModuleCat.biprodIsoProd M N).hom.hom x =
      ((biprod.fst : M ⊞ N ⟶ M).hom x, (biprod.snd : M ⊞ N ⟶ N).hom x) := by
  have hf : (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst k M N) =
      biprod.fst := by
    apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).mp
    simp
  have hs : (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd k M N) =
      biprod.snd := by
    apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).mp
    simp
  exact Prod.ext (congrArg (fun f : (M ⊞ N) ⟶ M ↦ f x) hf)
    (congrArg (fun f : (M ⊞ N) ⟶ N ↦ f x) hs)

private theorem moduleBiprodCoordinates_inl (M N : ModuleCat.{u} k) (x : M) :
    (ModuleCat.biprodIsoProd M N).hom.hom ((biprod.inl : M ⟶ M ⊞ N).hom x) = (x, 0) := by
  rw [moduleBiprodCoordinates_apply]
  apply Prod.ext
  · change ((biprod.inl : M ⟶ M ⊞ N) ≫ biprod.fst).hom x = x
    rw [biprod.inl_fst]
    rfl
  · change ((biprod.inl : M ⟶ M ⊞ N) ≫ biprod.snd).hom x = 0
    rw [biprod.inl_snd]
    rfl

private theorem moduleBiprodCoordinates_inr (M N : ModuleCat.{u} k) (x : N) :
    (ModuleCat.biprodIsoProd M N).hom.hom ((biprod.inr : N ⟶ M ⊞ N).hom x) = (0, x) := by
  rw [moduleBiprodCoordinates_apply]
  apply Prod.ext
  · change ((biprod.inr : N ⟶ M ⊞ N) ≫ biprod.fst).hom x = 0
    rw [biprod.inr_fst]
    rfl
  · change ((biprod.inr : N ⟶ M ⊞ N) ≫ biprod.snd).hom x = x
    rw [biprod.inr_snd]
    rfl

/-- Actual zero-chart sheaf one-forms in the original Kähler coordinates. -/
def zeroSheafOneCoordinates :
    (schemeFormsSheaf k 1).obj.obj (op (projectiveLineXOpen k)) ≅
      ModuleCat.of k Ω[Polynomial k⁄k] :=
  zeroSheafFormsCoordinates k 1 ≪≫
    ((exteriorPower.oneEquiv (Polynomial k) Ω[Polynomial k⁄k]).restrictScalars k).toModuleIso

/-- Actual infinity-chart sheaf one-forms in the original Kähler coordinates. -/
def infinitySheafOneCoordinates :
    (schemeFormsSheaf k 1).obj.obj (op (projectiveLineYOpen k)) ≅
      ModuleCat.of k Ω[Polynomial k⁄k] :=
  infinitySheafFormsCoordinates k 1 ≪≫
    ((exteriorPower.oneEquiv (Polynomial k) Ω[Polynomial k⁄k]).restrictScalars k).toModuleIso

/-- Actual sheaf one-forms on the geometric chart intersection. -/
def intersectionSheafOneCoordinates :
    (schemeFormsSheaf k 1).obj.obj (op (projectiveLineXOpen k ⊓ projectiveLineYOpen k)) ≅
      ModuleCat.of k Ω[LaurentPolynomial k⁄k] :=
  (schemeFormsSheaf k 1).obj.mapIso (eqToIso (projectiveLineOverlapChart_opensRange k)).op ≪≫
    overlapSheafFormsCoordinates k 1 ≪≫
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).restrictScalars k).toModuleIso

@[reassoc]
theorem zeroSheafOneCoordinates_restriction :
    (schemeFormsSheaf k 1).obj.map
        (homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
          projectiveLineXOpen k from inf_le_left)).op ≫
        (intersectionSheafOneCoordinates k).hom =
      (zeroSheafOneCoordinates k).hom ≫ ModuleCat.ofHom (chartZeroFormsMap k) := by
  simp only [intersectionSheafOneCoordinates, zeroSheafOneCoordinates, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  change (schemeFormsSheaf k 1).obj.map (homOfLE (overlapOpen_le_zeroOpen k)).op ≫ _ = _
  rw [zeroSheafFormsCoordinates_restriction_assoc]
  congr 1
  apply ModuleCat.hom_ext
  exact AlgebraDeRham.formsMap_oneEquiv k (chartZeroRingMap k)

@[reassoc]
theorem infinitySheafOneCoordinates_restriction :
    (schemeFormsSheaf k 1).obj.map
        (homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
          projectiveLineYOpen k from inf_le_right)).op ≫
        (intersectionSheafOneCoordinates k).hom =
      (infinitySheafOneCoordinates k).hom ≫ ModuleCat.ofHom (chartInfinityFormsMap k) := by
  simp only [intersectionSheafOneCoordinates, infinitySheafOneCoordinates, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  change (schemeFormsSheaf k 1).obj.map (homOfLE (overlapOpen_le_infinityOpen k)).op ≫ _ = _
  rw [infinitySheafFormsCoordinates_restriction_assoc]
  congr 1
  apply ModuleCat.hom_ext
  exact AlgebraDeRham.formsMap_oneEquiv k (chartInfinityRingMap k)

/-- The source coordinates of the original pair of chart one-forms. -/
def chartSheafOneCoordinates :
    ((schemeFormsSheaf k 1).obj.obj (op (projectiveLineXOpen k)) ⊞
      (schemeFormsSheaf k 1).obj.obj (op (projectiveLineYOpen k))) ≅
      ModuleCat.of k (Ω[Polynomial k⁄k] × Ω[Polynomial k⁄k]) :=
  biprod.mapIso (zeroSheafOneCoordinates k) (infinitySheafOneCoordinates k) ≪≫
    ModuleCat.biprodIsoProd _ _

/-- The target sign retains the original infinity-minus-zero convention. -/
def signedIntersectionSheafOneCoordinates :
    (schemeFormsSheaf k 1).obj.obj (op (projectiveLineXOpen k ⊓ projectiveLineYOpen k)) ≅
      ModuleCat.of k Ω[LaurentPolynomial k⁄k] :=
  intersectionSheafOneCoordinates k ≪≫
    (LinearEquiv.neg k (M := Ω[LaurentPolynomial k⁄k])).toModuleIso

theorem sheafOneDifference_coordinates :
    SheafCohomology.TwoOpenModules.sectionDifference k (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k))) (schemeFormsSheaf k 1)
        (projectiveLineXOpen k) (projectiveLineYOpen k) ≫
        (signedIntersectionSheafOneCoordinates k).hom =
      (chartSheafOneCoordinates k).hom ≫ ModuleCat.ofHom (chartFormsDifference k) := by
  apply biprod.hom_ext'
  · simp only [SheafCohomology.TwoOpenModules.sectionDifference,
      SheafCohomology.TwoOpenModules.linearPresheaf, Functor.id_obj,
      biprod.inl_desc_assoc, signedIntersectionSheafOneCoordinates, Iso.trans_hom]
    rw [zeroSheafOneCoordinates_restriction_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [chartSheafOneCoordinates, chartFormsDifference]
    rw [moduleBiprodCoordinates_inl]
    simp
  · simp only [SheafCohomology.TwoOpenModules.sectionDifference,
      SheafCohomology.TwoOpenModules.linearPresheaf, Functor.id_obj,
      biprod.inr_desc_assoc, signedIntersectionSheafOneCoordinates, Iso.trans_hom,
      Preadditive.neg_comp]
    rw [infinitySheafOneCoordinates_restriction_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [chartSheafOneCoordinates, chartFormsDifference]
    rw [moduleBiprodCoordinates_inr]
    simp

/-- The original Čech target is the actual one-form sheaf Čech cokernel. -/
def cechIsoSheafOneCokernel :
    ModuleCat.of k (CechH2 k) ≅
      cokernel (SheafCohomology.TwoOpenModules.sectionDifference k (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k)))
        (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) :=
  (formsCokernelEquiv k).toModuleIso.symm ≪≫
    (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (chartFormsDifference k))).symm ≪≫
      (cokernel.mapIso _ (ModuleCat.ofHom (chartFormsDifference k))
        (chartSheafOneCoordinates k) (signedIntersectionSheafOneCoordinates k)
        (sheafOneDifference_coordinates k)).symm

/-- The comparison is fixed by the original overlap representative and its actual Čech sign. -/
@[reassoc]
theorem cechIsoSheafOneCokernel_projection :
    cokernel.π (SheafCohomology.TwoOpenModules.sectionDifference k
      (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k)))
      (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) ≫
        (cechIsoSheafOneCokernel k).inv =
      (signedIntersectionSheafOneCoordinates k).hom ≫ ModuleCat.ofHom (overlapClass k) := by
  have hq : cokernel.π (ModuleCat.ofHom (chartFormsDifference k)) ≫
      (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (chartFormsDifference k))).hom ≫
      (formsCokernelEquiv k).toModuleIso.hom = ModuleCat.ofHom (overlapClass k) := by
    rw [← Category.assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact formsCokernelEquiv_mk k ω
  simp only [cechIsoSheafOneCokernel, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    cokernel.mapIso_hom, cokernel.π_desc_assoc]
  rw [hq]

/-- Original overlap classes map to the signed actual sheaf Čech projection. -/
@[reassoc]
theorem overlapClass_cechIsoSheafOneCokernel :
    ModuleCat.ofHom (overlapClass k) ≫ (cechIsoSheafOneCokernel k).hom =
      (signedIntersectionSheafOneCoordinates k).inv ≫
        cokernel.π (SheafCohomology.TwoOpenModules.sectionDifference k
          (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k)))
          (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) := by
  apply (cancel_epi (signedIntersectionSheafOneCoordinates k).hom).mp
  rw [← cechIsoSheafOneCokernel_projection_assoc]
  simp

/-- Actual zero-chart sheaf functions in the original polynomial coordinates. -/
def zeroSheafFunctionCoordinates :
    (schemeFormsSheaf k 0).obj.obj (op (projectiveLineXOpen k)) ≅
      ModuleCat.of k (Polynomial k) :=
  zeroSheafFormsCoordinates k 0 ≪≫
    ((exteriorPower.zeroEquiv (Polynomial k) Ω[Polynomial k⁄k]).restrictScalars k).toModuleIso

/-- Actual infinity-chart sheaf functions in the original polynomial coordinates. -/
def infinitySheafFunctionCoordinates :
    (schemeFormsSheaf k 0).obj.obj (op (projectiveLineYOpen k)) ≅
      ModuleCat.of k (Polynomial k) :=
  infinitySheafFormsCoordinates k 0 ≪≫
    ((exteriorPower.zeroEquiv (Polynomial k) Ω[Polynomial k⁄k]).restrictScalars k).toModuleIso

/-- Actual sheaf functions on the geometric chart intersection. -/
def intersectionSheafFunctionCoordinates :
    (schemeFormsSheaf k 0).obj.obj (op (projectiveLineXOpen k ⊓ projectiveLineYOpen k)) ≅
      ModuleCat.of k (LaurentPolynomial k) :=
  (schemeFormsSheaf k 0).obj.mapIso (eqToIso (projectiveLineOverlapChart_opensRange k)).op ≪≫
    overlapSheafFormsCoordinates k 0 ≪≫
      ((exteriorPower.zeroEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).restrictScalars k).toModuleIso

@[reassoc]
theorem zeroSheafFunctionCoordinates_restriction :
    (schemeFormsSheaf k 0).obj.map
        (homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
          projectiveLineXOpen k from inf_le_left)).op ≫
        (intersectionSheafFunctionCoordinates k).hom =
      (zeroSheafFunctionCoordinates k).hom ≫ ModuleCat.ofHom (chartZeroRingMap k).toLinearMap := by
  simp only [intersectionSheafFunctionCoordinates, zeroSheafFunctionCoordinates, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  change (schemeFormsSheaf k 0).obj.map (homOfLE (overlapOpen_le_zeroOpen k)).op ≫ _ = _
  rw [zeroSheafFormsCoordinates_restriction_assoc]
  congr 1
  apply ModuleCat.hom_ext
  exact AlgebraDeRham.formsMap_zeroEquiv k (chartZeroRingMap k)

@[reassoc]
theorem infinitySheafFunctionCoordinates_restriction :
    (schemeFormsSheaf k 0).obj.map
        (homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
          projectiveLineYOpen k from inf_le_right)).op ≫
        (intersectionSheafFunctionCoordinates k).hom =
      (infinitySheafFunctionCoordinates k).hom ≫ ModuleCat.ofHom (chartInfinityRingMap k).toLinearMap := by
  simp only [intersectionSheafFunctionCoordinates, infinitySheafFunctionCoordinates, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  change (schemeFormsSheaf k 0).obj.map (homOfLE (overlapOpen_le_infinityOpen k)).op ≫ _ = _
  rw [infinitySheafFormsCoordinates_restriction_assoc]
  congr 1
  apply ModuleCat.hom_ext
  exact AlgebraDeRham.formsMap_zeroEquiv k (chartInfinityRingMap k)

/-- The source coordinates of the original pair of chart functions. -/
def chartSheafFunctionCoordinates :
    ((schemeFormsSheaf k 0).obj.obj (op (projectiveLineXOpen k)) ⊞
      (schemeFormsSheaf k 0).obj.obj (op (projectiveLineYOpen k))) ≅
      ModuleCat.of k (Polynomial k × Polynomial k) :=
  biprod.mapIso (zeroSheafFunctionCoordinates k) (infinitySheafFunctionCoordinates k) ≪≫
    ModuleCat.biprodIsoProd _ _

/-- The target sign retains the original infinity-minus-zero convention. -/
def signedIntersectionSheafFunctionCoordinates :
    (schemeFormsSheaf k 0).obj.obj (op (projectiveLineXOpen k ⊓ projectiveLineYOpen k)) ≅
      ModuleCat.of k (LaurentPolynomial k) :=
  intersectionSheafFunctionCoordinates k ≪≫
    (LinearEquiv.neg k (M := LaurentPolynomial k)).toModuleIso

theorem sheafFunctionDifference_coordinates :
    SheafCohomology.TwoOpenModules.sectionDifference k (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k))) (schemeFormsSheaf k 0)
        (projectiveLineXOpen k) (projectiveLineYOpen k) ≫
        (signedIntersectionSheafFunctionCoordinates k).hom =
      (chartSheafFunctionCoordinates k).hom ≫ ModuleCat.ofHom (chartFunctionDifference k) := by
  apply biprod.hom_ext'
  · simp only [SheafCohomology.TwoOpenModules.sectionDifference,
      SheafCohomology.TwoOpenModules.linearPresheaf, Functor.id_obj,
      biprod.inl_desc_assoc, signedIntersectionSheafFunctionCoordinates, Iso.trans_hom]
    rw [zeroSheafFunctionCoordinates_restriction_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [chartSheafFunctionCoordinates, chartFunctionDifference]
    rw [moduleBiprodCoordinates_inl]
    simp
  · simp only [SheafCohomology.TwoOpenModules.sectionDifference,
      SheafCohomology.TwoOpenModules.linearPresheaf, Functor.id_obj,
      biprod.inr_desc_assoc, signedIntersectionSheafFunctionCoordinates, Iso.trans_hom,
      Preadditive.neg_comp]
    rw [infinitySheafFunctionCoordinates_restriction_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [chartSheafFunctionCoordinates, chartFunctionDifference]
    rw [moduleBiprodCoordinates_inr]
    simp


/-- The actual sheaf restriction difference on regular functions is surjective. -/
theorem sheafFunctionDifference_epi :
    Epi (SheafCohomology.TwoOpenModules.sectionDifference k (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k))) (schemeFormsSheaf k 0)
      (projectiveLineXOpen k) (projectiveLineYOpen k)) := by
  have : Epi (ModuleCat.ofHom (chartFunctionDifference k)) :=
    (ModuleCat.epi_iff_surjective _).2 (chartFunctionDifference_surjective k)
  have hcomp : Epi (SheafCohomology.TwoOpenModules.sectionDifference k (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k)))
      (schemeFormsSheaf k 0) (projectiveLineXOpen k) (projectiveLineYOpen k) ≫
      (signedIntersectionSheafFunctionCoordinates k).hom) := by
    rw [sheafFunctionDifference_coordinates]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).1 hcomp

end HodgeConjecture.ProjectiveLineDeRham
