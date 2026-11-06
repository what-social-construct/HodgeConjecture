module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineSheafCech
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSheafAcyclicity
public import HodgeConjecture.Realization.DeRham.ProjectiveLineHigherSheaves
public import HodgeConjecture.Realization.DeRham.TwoTermHypercohomology

@[expose] public section

/-!
# The actual projective-line degree-two scheme de Rham comparison

The original coordinate Čech quotient first becomes the cokernel of the
actual sheaf restriction difference. Affine vanishing and the actual
Mayer–Vietoris connecting map identify that cokernel with sheaf `H¹(Ω¹)`.
The actual two-term derived triangle then identifies it with degree-two
derived global sections of the original scheme's sheaf de Rham complex.

The scalar coordinates and nonzero Chern class are consequences of this
geometric comparison. They do not select the comparison. No singular or
Betti cohomology comparison is asserted here.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open KaehlerDifferential

namespace HodgeConjecture.ProjectiveLineDeRham

noncomputable section

universe u

variable (k : Type u) [Field k]

local notation "T" =>
  (𝟭 (TopCat.Sheaf (ModuleCat k) (projectiveLine k)))

attribute [local instance] HasDerivedCategory.standard

/-- Actual global first cohomology of the regular-function term vanishes. -/
theorem schemeZeroFormsH1_isZero :
    IsZero (((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 1).obj
      (schemeFormsSheaf k 0)) := by
  change IsZero (SheafCohomology.TwoOpenModules.Hobj k T ⊤ 1 (schemeFormsSheaf k 0))
  rw [← projectiveLineXOpen_sup_YOpen k]
  exact SheafCohomology.TwoOpenModules.isZero_firstCohomology_of_epi_difference k T
    (SheafCohomology.TwoOpenModules.injectiveRestrictions_identity k)
    (injectiveResolution (schemeFormsSheaf k 0)) (projectiveLineXOpen k) (projectiveLineYOpen k)
    (zeroChart_zeroFormsCohomology_isZero k 1 (by decide))
    (infinityChart_zeroFormsCohomology_isZero k 1 (by decide))
    (sheafFunctionDifference_epi k)

/-- Actual global second cohomology of the regular-function term vanishes. -/
theorem schemeZeroFormsH2_isZero :
    IsZero (((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 2).obj
      (schemeFormsSheaf k 0)) := by
  change IsZero (SheafCohomology.TwoOpenModules.Hobj k T ⊤ 2 (schemeFormsSheaf k 0))
  rw [← projectiveLineXOpen_sup_YOpen k]
  exact SheafCohomology.TwoOpenModules.isZero_successor_of_chartCohomology k T
    (SheafCohomology.TwoOpenModules.injectiveRestrictions_identity k)
    (injectiveResolution (schemeFormsSheaf k 0)) (projectiveLineXOpen k) (projectiveLineYOpen k) 1
    (overlap_zeroFormsCohomology_isZero k 1 (by decide))
    (zeroChart_zeroFormsCohomology_isZero k 2 (by decide))
    (infinityChart_zeroFormsCohomology_isZero k 2 (by decide))

/-- Degree-two derived global sections of the actual scheme de Rham sheaf complex. -/
abbrev SchemeH2 : ModuleCat.{u} k :=
  SchemeDeRham.hypercohomology k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) 2

/-- The actual derived inclusion of one-forms gives the two-term degree-two comparison. -/
def schemeH2IsoSheafH1 :
    SchemeH2 k ≅
      ((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 1).obj
        (schemeFormsSheaf k 1) :=
  BoundedBelowDerived.twoTermHypercohomologyIsoRightDerived
    (SheafHypercohomology.globalSections k (projectiveLine k))
    (SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)))
    (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn)
    (schemeZeroFormsH1_isZero k) (schemeZeroFormsH2_isZero k)

/-- The actual sheaf Čech cokernel is first cohomology through the resolution connecting map. -/
def sheafOneCokernelIsoH1 :
    cokernel (SheafCohomology.TwoOpenModules.sectionDifference k T
      (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) ≅
      ((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 1).obj
        (schemeFormsSheaf k 1) :=
  SheafCohomology.TwoOpenModules.cokernelIsoFirstCohomology k T
      (SheafCohomology.TwoOpenModules.injectiveRestrictions_identity k)
      (injectiveResolution (schemeFormsSheaf k 1)) (projectiveLineXOpen k) (projectiveLineYOpen k)
      (zeroChart_oneFormsCohomology_isZero k 1 (by decide))
      (infinityChart_oneFormsCohomology_isZero k 1 (by decide)) ≪≫
    eqToIso (by rw [projectiveLineXOpen_sup_YOpen]; rfl)

/-- The original injective-resolution connecting map, now evaluated on the whole scheme. -/
def sheafOneBoundary :
    (schemeFormsSheaf k 1).obj.obj (op (projectiveLineXOpen k ⊓ projectiveLineYOpen k)) ⟶
      ((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 1).obj
        (schemeFormsSheaf k 1) :=
  SheafCohomology.TwoOpenModules.boundary k T
      (SheafCohomology.TwoOpenModules.injectiveRestrictions_identity k)
      (injectiveResolution (schemeFormsSheaf k 1)) (projectiveLineXOpen k) (projectiveLineYOpen k) ≫
    eqToHom (by rw [projectiveLineXOpen_sup_YOpen]; rfl)

@[reassoc]
theorem sheafOneCokernelIsoH1_π_hom :
    cokernel.π (SheafCohomology.TwoOpenModules.sectionDifference k T
        (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) ≫
        (sheafOneCokernelIsoH1 k).hom = sheafOneBoundary k := by
  simp only [sheafOneCokernelIsoH1, Iso.trans_hom, eqToIso.hom,
    SheafCohomology.TwoOpenModules.cokernelIsoFirstCohomology_π_hom_assoc, sheafOneBoundary]

/-- The original degree-two coordinate complex computes actual scheme de Rham hypercohomology. -/
def schemeComparisonIso : ModuleCat.of k (CechH2 k) ≅ SchemeH2 k :=
  cechIsoSheafOneCokernel k ≪≫ sheafOneCokernelIsoH1 k ≪≫ (schemeH2IsoSheafH1 k).symm

/-- The geometric overlap-class map, constructed from the actual Mayer–Vietoris
boundary followed by the actual inverse two-term derived comparison. -/
def schemeOverlapClass : Ω[LaurentPolynomial k⁄k] →ₗ[k] SchemeH2 k :=
  ((signedIntersectionSheafOneCoordinates k).inv ≫ sheafOneBoundary k ≫
    (schemeH2IsoSheafH1 k).inv).hom

/-- The actual comparison carries original overlap representatives to their geometric boundary. -/
@[reassoc]
theorem overlapClass_schemeComparisonIso :
    ModuleCat.ofHom (overlapClass k) ≫ (schemeComparisonIso k).hom =
      ModuleCat.ofHom (schemeOverlapClass k) := by
  change _ = (signedIntersectionSheafOneCoordinates k).inv ≫ sheafOneBoundary k ≫
    (schemeH2IsoSheafH1 k).inv
  simp only [schemeComparisonIso, Iso.trans_hom, Iso.symm_hom]
  rw [overlapClass_cechIsoSheafOneCokernel_assoc, sheafOneCokernelIsoH1_π_hom_assoc]

@[simp]
theorem schemeComparisonIso_overlapClass (ω : Ω[LaurentPolynomial k⁄k]) :
    (schemeComparisonIso k).hom (overlapClass k ω) = schemeOverlapClass k ω :=
  congrArg (fun φ : ModuleCat.of k Ω[LaurentPolynomial k⁄k] ⟶ SchemeH2 k ↦ φ ω)
    (overlapClass_schemeComparisonIso k)

/-- The actual coordinate-transition Chern class in scheme de Rham hypercohomology. -/
def schemeChernCoordinate : SchemeH2 k :=
  (schemeComparisonIso k).hom (chernCoordinate k)

/-- The scheme Chern coordinate is the actual connecting class of `d log T`. -/
theorem schemeOverlapClass_dlogT :
    schemeOverlapClass k (LaurentDeRham.dlogT k) = schemeChernCoordinate k := by
  rw [← schemeComparisonIso_overlapClass]
  rfl

/-- Scalar coordinates obtained after the actual scheme comparison. -/
def schemeResidueEquiv : SchemeH2 k ≃ₗ[k] k :=
  (schemeComparisonIso k).toLinearEquiv.symm.trans (cechResidueEquiv k)

@[simp]
theorem schemeResidueEquiv_comparison (z : CechH2 k) :
    schemeResidueEquiv k ((schemeComparisonIso k).hom z) = cechResidue k z := by
  change cechResidue k ((schemeComparisonIso k).inv ((schemeComparisonIso k).hom z)) = _
  rw [Iso.hom_inv_id_apply]

@[simp]
theorem schemeResidueEquiv_chernCoordinate :
    schemeResidueEquiv k (schemeChernCoordinate k) = 1 := by
  rw [schemeChernCoordinate, schemeResidueEquiv_comparison, cechResidue_chernCoordinate]

theorem schemeChernCoordinate_ne_zero : schemeChernCoordinate k ≠ 0 := by
  intro h
  have hh := congrArg (schemeResidueEquiv k) h
  rw [schemeResidueEquiv_chernCoordinate, map_zero] at hh
  exact one_ne_zero hh

/-- Every actual scheme degree-two class has its computed residue coordinate. -/
theorem schemeClass_eq_residue_smul (z : SchemeH2 k) :
    z = schemeResidueEquiv k z • schemeChernCoordinate k := by
  apply (schemeResidueEquiv k).injective
  rw [map_smul, schemeResidueEquiv_chernCoordinate, smul_eq_mul, mul_one]

end

end HodgeConjecture.ProjectiveLineDeRham
