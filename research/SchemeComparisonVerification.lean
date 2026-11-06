module

import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass
import HodgeConjecture.Realization.DeRham.OpenImmersionTrivialization
import HodgeConjecture.Realization.DeRham.SheafHypercohomology
import HodgeConjecture.SheafCohomology.LinearCoefficients
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Lean.Util.CollectAxioms

/-!
Focused checks for actual scheme sheaves, their canonical atlas units and
restrictions, and the original projective-line Čech quotient. Derived
single-sheaf comparisons use constructed injective resolutions. Every
comparison used below is proved by the imported construction; no desired
comparison or cohomological vanishing is assumed by these examples.

The scheme-level constructions are tested over arbitrary fields, including
characteristic two. The Čech boundary reduction is also tested over a ring
that is not a field. No Betti or Hodge comparison is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open KaehlerDifferential HodgeConjecture HodgeConjecture.ProjectiveLineDeRham
open HodgeConjecture.SchemeCycles HodgeConjecture.ProjectiveLineCycles

noncomputable section

universe u

section ActualAtlas

variable (k : Type u) [Field k]

-- The geometric Mayer–Vietoris square covers the original scheme, including in small characteristic.
example : (projectiveLineMayerVietorisSquare k).X₄ = (⊤ : (projectiveLine k).Opens) := rfl

example : projectiveLineXOpen k ⊔ projectiveLineYOpen k = ⊤ :=
  projectiveLineXOpen_sup_YOpen k

-- Both original coordinate restrictions factor through their actual open subschemes.
example : (projectiveLineOverlapOpenIso k).hom ≫
      (projectiveLine k).homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
        projectiveLineYOpen k from inf_le_right) ≫ (projectiveLineYOpen k).ι =
    (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫
      projectiveLineYChart k := by
  rw [projectiveLineOverlapOpenIso_hom_Y_assoc, projectiveLineYOpenIso_hom_ι]

-- Applying the actual canonical unit and then sheaf coordinates recovers every old representative.
example (n : ℕ) :
    (toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineXOpen k)) ≫
          (zeroSheafFormsCoordinates k n).hom ≫ (zeroFormsCoordinates k n).toModuleIso.inv = 𝟙 _ := by
  rw [zeroSheafFormsCoordinates_unit_assoc, Iso.hom_inv_id]

example (n : ℕ) :
    (toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app
          (op (projectiveLineOverlapChart k).opensRange) ≫
          (overlapSheafFormsCoordinates k n).hom ≫ (overlapFormsCoordinates k n).toModuleIso.inv = 𝟙 _ := by
  rw [overlapSheafFormsCoordinates_unit_assoc, Iso.hom_inv_id]

-- Actual sheaf restriction recovers the original chart map on all one-forms, including dx.
example :
    ((zeroSheafOneCoordinates k).inv ≫ (schemeFormsSheaf k 1).obj.map
      (homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
        projectiveLineXOpen k from inf_le_left)).op ≫
        (intersectionSheafOneCoordinates k).hom = ModuleCat.ofHom (chartZeroFormsMap k)) ∧
      chartZeroFormsMap k (D k (Polynomial k) Polynomial.X) =
        D k (LaurentPolynomial k) (chartZeroRingMap k Polynomial.X) := by
  constructor
  · rw [zeroSheafOneCoordinates_restriction, Iso.inv_hom_id_assoc]
  · exact chartZeroFormsMap_D k Polynomial.X

-- The other actual restriction retains the inverse-coordinate map and its differential.
example :
    ((infinitySheafOneCoordinates k).inv ≫ (schemeFormsSheaf k 1).obj.map
      (homOfLE (show projectiveLineXOpen k ⊓ projectiveLineYOpen k ≤
        projectiveLineYOpen k from inf_le_right)).op ≫
        (intersectionSheafOneCoordinates k).hom = ModuleCat.ofHom (chartInfinityFormsMap k)) ∧
      chartInfinityFormsMap k (D k (Polynomial k) Polynomial.X) =
        D k (LaurentPolynomial k) (chartInfinityRingMap k Polynomial.X) := by
  constructor
  · rw [infinitySheafOneCoordinates_restriction, Iso.inv_hom_id_assoc]
  · exact chartInfinityFormsMap_D k Polynomial.X

-- The unit is canonically invertible in a higher exterior degree as well.
example : IsIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
    (SchemeDeRham.formsPresheaf k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) 3)).app (op (projectiveLineYOpen k))) :=
  infinityFormsSheafUnit_isIso k 3

end ActualAtlas

-- These are actual field/sheaf examples with no characteristic-zero instance.
example : projectiveLineXOpen (ZMod 2) ⊔ projectiveLineYOpen (ZMod 2) = ⊤ :=
  projectiveLineXOpen_sup_YOpen (ZMod 2)

example : Nonempty
    ((schemeFormsSheaf (ZMod 2) 1).obj.obj
        (op (projectiveLineOverlapChart (ZMod 2)).opensRange) ≅
      ModuleCat.of (ZMod 2) (⋀[LaurentPolynomial (ZMod 2)]^1
        Ω[LaurentPolynomial (ZMod 2)⁄ZMod 2])) :=
  ⟨overlapSheafFormsCoordinates (ZMod 2) 1⟩

section ActualDerivedSections

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k]

-- A single actual sheaf has the same positive cohomology under both proved derived constructions.
example : Nonempty
    (SheafHypercohomology.hypercohomology k (projectiveLine k)
        ((CochainComplex.single₀ _).obj (schemeFormsSheaf k 0)) 2 ≅
      ((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 2).obj
        (schemeFormsSheaf k 0)) :=
  ⟨SheafHypercohomology.singleIsoRightDerived k (projectiveLine k) (schemeFormsSheaf k 0) 2⟩

-- Forgetting coefficients commutes with the ordinary derived construction on that same sheaf.
example : Nonempty
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).obj
        (((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 1).obj
          (schemeFormsSheaf k 1)) ≅
      ((SheafHypercohomology.globalSections k (projectiveLine k) ⋙
        forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).rightDerived 1).obj
          (schemeFormsSheaf k 1)) :=
  ⟨BoundedBelowDerived.rightDerivedPostcomposeIso
    (SheafHypercohomology.globalSections k (projectiveLine k))
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) (schemeFormsSheaf k 1) 1⟩

-- Derived maps preserve the actual identity and composition on the original sheaf complex.
example : SheafHypercohomology.derivedGlobalSectionsMap k (projectiveLine k)
      (𝟙 (SchemeDeRham.sheafComplex k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)))) = 𝟙 _ := by
  have h : SheafHypercohomology.nonnegativeMap k (projectiveLine k)
      (𝟙 (SchemeDeRham.sheafComplex k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)))) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact HomologicalComplex.extendMap_id _ _
  unfold SheafHypercohomology.derivedGlobalSectionsMap
  rw [h, DerivedCategory.Plus.Q.map_id]
  exact (SheafHypercohomology.globalSections k (projectiveLine k)).rightDerivedFunctorPlus.map_id _

example (φ ψ : SchemeDeRham.sheafComplex k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) ⟶
      SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))) :
    SheafHypercohomology.derivedGlobalSectionsMap k (projectiveLine k) (φ ≫ ψ) =
      SheafHypercohomology.derivedGlobalSectionsMap k (projectiveLine k) φ ≫
        SheafHypercohomology.derivedGlobalSectionsMap k (projectiveLine k) ψ := by
  have h : SheafHypercohomology.nonnegativeMap k (projectiveLine k) (φ ≫ ψ) =
      SheafHypercohomology.nonnegativeMap k (projectiveLine k) φ ≫
        SheafHypercohomology.nonnegativeMap k (projectiveLine k) ψ := by
    apply ObjectProperty.hom_ext
    exact HomologicalComplex.extendMap_comp _ _ _
  simp only [SheafHypercohomology.derivedGlobalSectionsMap, h, Functor.map_comp]

-- The coefficient functor really retains the original sections.
example (U : (projectiveLine k).Opens) :
    ((SheafCohomology.LinearCoefficients.underlying k (projectiveLine k)).obj
      (schemeFormsSheaf k 1)).obj.obj (op U) =
        (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).obj
          ((schemeFormsSheaf k 1).obj.obj (op U)) := rfl

end ActualDerivedSections

section OriginalCechQuotient

variable (k : Type u) [CommRing k]

-- Every exact overlap one-form is already an actual difference of chart one-forms.
example (f : LaurentPolynomial k) :
    D k (LaurentPolynomial k) f ∈ LinearMap.range (chartFormsDifference k) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := chartFunctionDifference_surjective k f
  refine ⟨(D k (Polynomial k) p, D k (Polynomial k) q), ?_⟩
  change chartInfinityFormsMap k (D k (Polynomial k) q) -
      chartZeroFormsMap k (D k (Polynomial k) p) = D k (LaurentPolynomial k) f
  rw [chartInfinityFormsMap_D, chartZeroFormsMap_D, ← hpq]
  exact (D k (LaurentPolynomial k)).map_sub _ _ |>.symm

-- The new quotient has precisely the same original incoming relations, before any cohomology comparison.
example (x : CechOne k) : cechIncomingForm k x ∈ LinearMap.range (chartFormsDifference k) := by
  rw [← range_cechIncomingForm_eq]
  exact ⟨x, rfl⟩

example (ω : Ω[LaurentPolynomial k⁄k]) :
    (formsCokernelEquiv k).symm (overlapClass k ω) =
      (LinearMap.range (chartFormsDifference k)).mkQ ω := by
  rw [← formsCokernelEquiv_mk]
  exact (formsCokernelEquiv k).symm_apply_apply _

-- The old logarithmic Chern representative survives this actual quotient comparison unchanged.
theorem schemeComparison_logarithmicRepresentative : formsCokernelEquiv k
    ((LinearMap.range (chartFormsDifference k)).mkQ
      (AffineDeRham.logarithmicDifferential k (LaurentPolynomial k)
        (LaurentDeRham.variableUnit k))) = chernCoordinate k := by
  rw [formsCokernelEquiv_mk]
  rfl

end OriginalCechQuotient

-- Both directions of the cokernel comparison retain the original overlap map and its actual MV sign.
example (k : Type u) [Field k] :
    (signedIntersectionSheafOneCoordinates k).inv ≫
      cokernel.π (SheafCohomology.TwoOpenModules.sectionDifference k
        (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k)))
        (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) ≫
        (cechIsoSheafOneCokernel k).inv = ModuleCat.ofHom (overlapClass k) := by
  rw [cechIsoSheafOneCokernel_projection, Iso.inv_hom_id_assoc]

example (k : Type u) [Field k] :
    (signedIntersectionSheafOneCoordinates k).inv ≫
      cokernel.π (SheafCohomology.TwoOpenModules.sectionDifference k
        (𝟭 (TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k)))
        (schemeFormsSheaf k 1) (projectiveLineXOpen k) (projectiveLineYOpen k)) =
      ModuleCat.ofHom (overlapClass k) ≫ (cechIsoSheafOneCokernel k).hom := by
  apply (cancel_mono (cechIsoSheafOneCokernel k).inv).mp
  rw [Category.assoc, cechIsoSheafOneCokernel_projection]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]

-- The overlap dlog class remains nonzero in characteristic two after quotienting by chart forms.
example : (LinearMap.range (chartFormsDifference (ZMod 2))).mkQ
    (AffineDeRham.logarithmicDifferential (ZMod 2) (LaurentPolynomial (ZMod 2))
      (LaurentDeRham.variableUnit (ZMod 2))) ≠ 0 := by
  intro h
  apply chernCoordinate_ne_zero (ZMod 2)
  have hh := congrArg (formsCokernelEquiv (ZMod 2)) h
  rw [schemeComparison_logarithmicRepresentative, map_zero] at hh
  exact hh

-- Exactness reduction also works over a coefficient ring with zero divisors.
example (x : CechOne (ZMod 6)) :
    cechIncomingForm (ZMod 6) x ∈ LinearMap.range (chartFormsDifference (ZMod 6)) := by
  rw [← range_cechIncomingForm_eq]
  exact ⟨x, rfl⟩

-- The actual sheaf Čech cokernel contains the nonzero original Chern class.
example : (cechIsoSheafOneCokernel ℚ).hom (chernCoordinate ℚ) ≠ 0 := by
  intro h
  apply chernCoordinate_ne_zero ℚ
  have hh := congrArg (cechIsoSheafOneCokernel ℚ).inv h
  simpa only [Iso.hom_inv_id_apply, map_zero] using hh

section ActualSchemeEndpoint

variable (k : Type u) [Field k]

-- The target is the independently defined derived global sections of the original scheme complex.
example : SchemeH2 k = SchemeDeRham.hypercohomology k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) 2 := rfl

example (z : SchemeH2 k) : z = schemeResidueEquiv k z • schemeChernCoordinate k :=
  schemeClass_eq_residue_smul k z

example (z : CechH2 k) : schemeResidueEquiv k ((schemeComparisonIso k).hom z) =
    cechResidue k z := schemeResidueEquiv_comparison k z

-- The vanishing used by the two-term bridge is proved for the actual regular-function sheaf.
example : IsZero (((SheafHypercohomology.globalSections k (projectiveLine k)).rightDerived 2).obj
    (schemeFormsSheaf k 0)) := schemeZeroFormsH2_isZero k

end ActualSchemeEndpoint

example : schemeChernCoordinate (ZMod 2) ≠ 0 := schemeChernCoordinate_ne_zero (ZMod 2)

example : schemeResidueEquiv (ZMod 2) (schemeChernCoordinate (ZMod 2)) = 1 :=
  schemeResidueEquiv_chernCoordinate (ZMod 2)

section ActualOrdinaryChowSource

variable (k : Type u) [Field k] [IsAlgClosed k]

-- The actual integral cycle quotient maps coefficient-one points to the normalized scheme class.
example (x : projectiveLine k) (hx : x ≠ genericPoint (projectiveLine k)) :
    ProjectiveLineSchemeCycleClass.integralCycleClass k
      (classMap (dimensionFunction k) 0 (pointCycle k ℤ x hx)) = schemeChernCoordinate k :=
  ProjectiveLineSchemeCycleClass.integralCycleClass_pointCycle k x hx

variable [CharZero k]

example (x : projectiveLine k) (hx : x ≠ genericPoint (projectiveLine k)) :
    RestrictScalars.addEquiv ℚ k (SchemeH2 k)
      (ProjectiveLineSchemeCycleClass.cycleClass k
        (rationalClassMap (dimensionFunction k) 0 (pointCycle k ℚ x hx))) =
      schemeChernCoordinate k := ProjectiveLineSchemeCycleClass.cycleClass_pointCycle k x hx

-- The new realization commutes with the original ordinary map on every existing rational Chow class.
example (z : RationalChowGroup (dimensionFunction k) 0) :
    (schemeComparisonIso k).hom
      (RestrictScalars.addEquiv ℚ k (CechH2 k) (ProjectiveLineCycleClass.cycleClass k z)) =
      RestrictScalars.addEquiv ℚ k (SchemeH2 k) (ProjectiveLineSchemeCycleClass.cycleClass k z) :=
  ProjectiveLineSchemeCycleClass.cycleClass_comparison k z

example (z : ChowGroup (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (SchemeH2 k)
      (ProjectiveLineSchemeCycleClass.cycleClass k (chowRationalize (dimensionFunction k) 0 z)) =
      ProjectiveLineSchemeCycleClass.integralCycleClass k z :=
  ProjectiveLineSchemeCycleClass.cycleClass_chowRationalize k z

-- Every original principal-relation carrier vanishes; no invariant-degree premise is supplied.
example (d : PrincipalRelationData (dimensionFunction k) 0) :
    ProjectiveLineSchemeCycleClass.cycleClass k
      (rationalClassMap (dimensionFunction k) 0 (cyclesOfDegreeRationalize (dimensionFunction k) 0
        (principalRelation (dimensionFunction k) 0 d))) = 0 :=
  ProjectiveLineSchemeCycleClass.cycleClass_principalRelation k d

end ActualOrdinaryChowSource

example : ProjectiveLineSchemeCycleClass.integralCycleClass ℂ
    (ProjectiveLineCycleClass.integralInfinityClass ℂ) = schemeChernCoordinate ℂ :=
  ProjectiveLineSchemeCycleClass.integralCycleClass_pointCycle ℂ _ _

example : schemeResidueEquiv ℂ
    (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
      (ProjectiveLineSchemeCycleClass.cycleClass ℂ
        ((-3 / 2 : ℚ) • ProjectiveLineCycleClass.rationalInfinityClass ℂ))) = -3 / 2 := by
  rw [ProjectiveLineSchemeCycleClass.residue_cycleClass, map_smul, smul_eq_mul,
    ProjectiveLineCycleClass.rationalChowDegree_infinity, mul_one]
  norm_num

example : ProjectiveLineSchemeCycleClass.cycleClass ℂ ≠ 0 :=
  ProjectiveLineSchemeCycleClass.cycleClass_ne_zero ℂ

-- Complex cohomology coefficients outside the rational scalar image remain outside the rational cycle image.
example : (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)).symm
    (Complex.I • schemeChernCoordinate ℂ) ∉ Set.range (ProjectiveLineSchemeCycleClass.cycleClass ℂ) := by
  apply ProjectiveLineSchemeCycleClass.scalar_chernCoordinate_not_mem_cycleClass_range ℂ Complex.I
  rintro ⟨q, hq⟩
  have him := congrArg Complex.im hq
  norm_num at him

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `AlgebraicGeometry.projectiveLineXOpen_sup_YOpen,
    `AlgebraicGeometry.projectiveLineOverlapChart_opensRange,
    `AlgebraicGeometry.projectiveLineMayerVietorisSquare,
    `HodgeConjecture.SchemeDeRham.sectionBaseMap_restrict,
    `HodgeConjecture.AlgebraDeRham.formsMap_deRhamDifferential,
    `HodgeConjecture.SchemeDeRham.affineLineFormsPresheaf_isSheaf,
    `HodgeConjecture.SchemeDeRham.laurentFormsSheafUnit_isIso,
    `HodgeConjecture.SchemeDeRham.openImmersionSectionEquiv,
    `HodgeConjecture.SchemeDeRham.openImmersionFormsSheafIso_unit,
    `HodgeConjecture.SchemeDeRham.underRangeOneFormsTrivialization,
    `HodgeConjecture.SchemeDeRham.underRangeOneFormsAddEquiv_naturality,
    `HodgeConjecture.SheafHypercohomology.derivedGlobalSections,
    `HodgeConjecture.SheafHypercohomology.comparison_naturality,
    `HodgeConjecture.BoundedBelowDerived.injectiveResolutionDerivedIso,
    `HodgeConjecture.BoundedBelowDerived.singleHypercohomologyIsoRightDerived,
    `HodgeConjecture.BoundedBelowDerived.rightDerivedPostcomposeIso,
    `HodgeConjecture.SheafHypercohomology.singleIsoRightDerived,
    `HodgeConjecture.SchemeDeRham.hypercohomology,
    `HodgeConjecture.SheafCohomology.LinearCoefficients.cechAcyclicInjectives,
    `HodgeConjecture.SheafCohomology.TwoOpenModules.coverShortComplex_shortExact,
    `HodgeConjecture.SheafCohomology.TwoOpenModules.cokernelIsoFirstCohomology,
    `HodgeConjecture.SheafCohomology.TwoOpenModules.isZero_successor_of_chartCohomology,
    `HodgeConjecture.ProjectiveLineDeRham.overlapChart_comp_structureMorphism,
    `HodgeConjecture.ProjectiveLineDeRham.zeroFormsCoordinates_restriction,
    `HodgeConjecture.ProjectiveLineDeRham.infinityFormsCoordinates_restriction,
    `HodgeConjecture.ProjectiveLineDeRham.overlapFormsSheafUnit_isIso,
    `HodgeConjecture.ProjectiveLineDeRham.zeroSheafFormsCoordinates_unit,
    `HodgeConjecture.ProjectiveLineDeRham.overlapSheafFormsCoordinates_unit,
    `HodgeConjecture.ProjectiveLineDeRham.zeroSheafFormsCoordinates_restriction,
    `HodgeConjecture.ProjectiveLineDeRham.infinitySheafFormsCoordinates_restriction,
    `HodgeConjecture.ProjectiveLineDeRham.chartFunctionDifference_surjective,
    `HodgeConjecture.ProjectiveLineDeRham.range_cechIncomingForm_eq,
    `HodgeConjecture.ProjectiveLineDeRham.ker_overlapClass_eq,
    `HodgeConjecture.ProjectiveLineDeRham.formsCokernelEquiv_mk,
    `HodgeConjecture.ProjectiveLineDeRham.sheafOneDifference_coordinates,
    `HodgeConjecture.ProjectiveLineDeRham.cechIsoSheafOneCokernel,
    `HodgeConjecture.ProjectiveLineDeRham.cechIsoSheafOneCokernel_projection,
    `HodgeConjecture.ProjectiveLineDeRham.sheafFunctionDifference_epi,
    `HodgeConjecture.ProjectiveLineDeRham.higherSchemeFormsSheaf_isZero,
    `HodgeConjecture.ProjectiveLineDeRham.zeroChart_oneFormsCohomology_isZero,
    `HodgeConjecture.ProjectiveLineDeRham.overlap_oneFormsCohomology_isZero,
    `HodgeConjecture.BoundedBelowDerived.twoTermHypercohomologyIsoRightDerived,
    `HodgeConjecture.ProjectiveLineDeRham.schemeZeroFormsH1_isZero,
    `HodgeConjecture.ProjectiveLineDeRham.schemeZeroFormsH2_isZero,
    `HodgeConjecture.ProjectiveLineDeRham.schemeH2IsoSheafH1,
    `HodgeConjecture.ProjectiveLineDeRham.sheafOneCokernelIsoH1,
    `HodgeConjecture.ProjectiveLineDeRham.schemeComparisonIso,
    `HodgeConjecture.ProjectiveLineDeRham.schemeResidueEquiv_comparison,
    `HodgeConjecture.ProjectiveLineDeRham.schemeResidueEquiv_chernCoordinate,
    `HodgeConjecture.ProjectiveLineDeRham.schemeChernCoordinate_ne_zero,
    `HodgeConjecture.ProjectiveLineDeRham.schemeClass_eq_residue_smul,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.integralCycleClass_principalRelation,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.cycleClass_comparison,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.cycleClass_pointCycle,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.cycleClass_chowRationalize,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.cycleClass_principalRelation,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.cycleClass_ne_zero,
    `HodgeConjecture.ProjectiveLineSchemeCycleClass.scalar_chernCoordinate_not_mem_cycleClass_range]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
