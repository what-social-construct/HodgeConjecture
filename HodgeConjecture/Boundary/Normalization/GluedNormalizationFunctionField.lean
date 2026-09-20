import HodgeConjecture.Boundary.Normalization.GluedNormalizationIntegrality
import HodgeConjecture.Boundary.Normalization.GluedNormalizationSurjectivity
import HodgeConjecture.Cycles.FunctionFieldComparison
import Mathlib.RingTheory.Localization.Integral

/-!
# The function field of the original glued normalization

For a finite ambient extension, each original integral-closure chart has
that ambient field as its fraction field. The actual chart generic-stalk
maps identify the intrinsic function field with this same marked field.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles NormalizationInertia

noncomputable section

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable [FiniteDimensional X.functionField N]

local instance comparisonAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

local instance comparisonScalarTower (U : NonemptyAffineChart X) :
    IsScalarTower Γ(X, U.val) X.functionField N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance comparisonBaseFractionRing (U : NonemptyAffineChart X) :
    IsFractionRing Γ(X, U.val) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X U.val U.property.1

local instance comparisonNormalizationFractionRing (U : NonemptyAffineChart X) :
    IsFractionRing (normalizedCoordinateRing Γ(X, U.val) N) N :=
  integralClosure.isFractionRing_of_finite_extension X.functionField N

local instance comparisonChartIntegral (U : NonemptyAffineChart X) :
    IsIntegral ((affineNormalizationDiagram X N).obj U) := by
  change IsIntegral (normalizedAffineModel Γ(X, U.val) N)
  unfold normalizedAffineModel
  infer_instance

local instance comparisonAffineIntegral (B : Type u) [CommRing B] [Algebra B N] :
    IsIntegral (normalizedAffineModel B N) := by
  unfold normalizedAffineModel
  infer_instance

local instance comparisonChartFieldAlgebra (U : NonemptyAffineChart X) :
    Algebra (normalizedCoordinateRing Γ(X, U.val) N)
      ((affineNormalizationDiagram X N).obj U).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (.of (normalizedCoordinateRing Γ(X, U.val) N))

local instance comparisonChartFieldFractionRing (U : NonemptyAffineChart X) :
    IsFractionRing (normalizedCoordinateRing Γ(X, U.val) N)
      ((affineNormalizationDiagram X N).obj U).functionField :=
  functionField_isFractionRing_of_affine (.of (normalizedCoordinateRing Γ(X, U.val) N))

local instance comparisonBaseSurjective : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance comparisonAffineDominant (U : NonemptyAffineChart X) :
    IsDominant (normalizedModelToBase Γ(X, U.val) N) := by
  apply specMap_isDominant_of_injective
  intro b c h
  apply (X.germToFunctionField_injective U.val)
  apply (algebraMap X.functionField N).injective
  exact congrArg (fun t : normalizedCoordinateRing Γ(X, U.val) N => (t : N)) h

/-- The original affine chart's function field, expressed in its ambient finite extension. -/
def affineNormalizationFunctionFieldEquiv (U : NonemptyAffineChart X) :
    ((affineNormalizationDiagram X N).obj U).functionField ≃+* N :=
  (IsLocalization.algEquiv (nonZeroDivisors (normalizedCoordinateRing Γ(X, U.val) N))
    ((affineNormalizationDiagram X N).obj U).functionField N).toRingEquiv

/-- Integral coordinates retain their original ambient-field values. -/
theorem affineNormalizationFunctionFieldEquiv_algebraMap
    (U : NonemptyAffineChart X) (t : normalizedCoordinateRing Γ(X, U.val) N) :
    affineNormalizationFunctionFieldEquiv X N U
        (algebraMap (normalizedCoordinateRing Γ(X, U.val) N)
          ((affineNormalizationDiagram X N).obj U).functionField t) = (t : N) :=
  (IsLocalization.algEquiv (nonZeroDivisors (normalizedCoordinateRing Γ(X, U.val) N))
    ((affineNormalizationDiagram X N).obj U).functionField N).commutes t

/-- Comparison through an original chart, using its actual generic-stalk isomorphism. -/
def gluedNormalizationFunctionFieldEquivAt (U : NonemptyAffineChart X) :
    (gluedNormalizationModel X N).functionField ≃+* N :=
  (functionFieldEquivOfOpenImmersion (normalizationChartToGlued X N U)).trans
    (affineNormalizationFunctionFieldEquiv X N U)

/-- The chart comparison is the actual chart pullback followed by affine fractions. -/
theorem gluedNormalizationFunctionFieldEquivAt_apply_chart
    (U : NonemptyAffineChart X) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U a =
      affineNormalizationFunctionFieldEquiv X N U
        (functionFieldMapOfDominant (normalizationChartToGlued X N U) a) := rfl

private theorem normalizationChartFieldEquiv_restriction
    {U V : NonemptyAffineChart X} (f : U ⟶ V)
    (a : ((affineNormalizationDiagram X N).obj V).functionField) :
    affineNormalizationFunctionFieldEquiv X N U
        (functionFieldMapOfDominant ((affineNormalizationDiagram X N).map f) a) =
      affineNormalizationFunctionFieldEquiv X N V a := by
  letI : Algebra Γ(X, V.val) Γ(X, U.val) :=
    (X.presheaf.map (homOfLE (leOfHom f)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, V.val) Γ(X, U.val) N :=
    sectionRestriction_ambientScalarTower V.val U.val N (leOfHom f)
  let r := CommRingCat.ofHom
    (normalizationBaseChangeMap (B := Γ(X, V.val)) (C := Γ(X, U.val)) (E := N)).toRingHom
  letI : IsDominant (Spec.map r) :=
    inferInstanceAs (IsDominant ((affineNormalizationDiagram X N).map f))
  have h : (affineNormalizationFunctionFieldEquiv X N U).toRingHom.comp
      (functionFieldMapOfDominant ((affineNormalizationDiagram X N).map f)).hom =
      (affineNormalizationFunctionFieldEquiv X N V).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := normalizedCoordinateRing Γ(X, V.val) N)
    intro t
    change affineNormalizationFunctionFieldEquiv X N U
      (functionFieldMapOfDominant ((affineNormalizationDiagram X N).map f)
        (algebraMap (normalizedCoordinateRing Γ(X, V.val) N) _ t)) = _
    erw [functionFieldMapOfDominant_spec_algebraMap r t]
    erw [affineNormalizationFunctionFieldEquiv_algebraMap X N U (r t),
      affineNormalizationFunctionFieldEquiv_algebraMap X N V t]
    rfl
  exact DFunLike.congr_fun h a

/-- Restricting an original chart leaves its function-field comparison unchanged. -/
theorem gluedNormalizationFunctionFieldEquivAt_restriction
    {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    gluedNormalizationFunctionFieldEquivAt X N U =
      gluedNormalizationFunctionFieldEquivAt X N V := by
  ext a
  have he : functionFieldMapOfDominant (normalizationChartToGlued X N U) =
      functionFieldMapOfDominant (normalizationChartToGlued X N V) ≫
        functionFieldMapOfDominant ((affineNormalizationDiagram X N).map f) := by
    rw [← functionFieldMapOfDominant_comp]
    congr 1
    exact (normalizationChartToGlued_naturality X N f).symm
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) a
  change functionFieldMapOfDominant (normalizationChartToGlued X N U) a =
    functionFieldMapOfDominant ((affineNormalizationDiagram X N).map f)
      (functionFieldMapOfDominant (normalizationChartToGlued X N V) a) at h
  change gluedNormalizationFunctionFieldEquivAt X N U a = _
  change affineNormalizationFunctionFieldEquiv X N U
    (functionFieldMapOfDominant (normalizationChartToGlued X N U) a) = _
  rw [h, normalizationChartFieldEquiv_restriction]
  rfl

/-- The comparison is independent of the original nonempty affine chart. -/
theorem gluedNormalizationFunctionFieldEquivAt_eq (U V : NonemptyAffineChart X) :
    gluedNormalizationFunctionFieldEquivAt X N U =
      gluedNormalizationFunctionFieldEquivAt X N V := by
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.val.isOpen V.val.isOpen
    (Set.nonempty_coe_sort.mp U.property.2) (Set.nonempty_coe_sort.mp V.property.2)
  obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter
    U.property.1 V.property.1 x ⟨hxU, hxV⟩
  let W : NonemptyAffineChart X :=
    ⟨X.basicOpen r, U.property.1.basicOpen r, ⟨⟨x, hxr⟩⟩⟩
  exact (gluedNormalizationFunctionFieldEquivAt_restriction X N
    (homOfLE (X.basicOpen_le r) : W ⟶ U)).symm.trans
    (gluedNormalizationFunctionFieldEquivAt_restriction X N
      (homOfLE (hrs.trans_le (X.basicOpen_le s)) : W ⟶ V))

/-- The comparison preserves the actual structural function-field embedding. -/
theorem gluedNormalizationFunctionFieldEquivAt_toBase
    (U : NonemptyAffineChart X) (a : X.functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U
        (functionFieldMapOfDominant (gluedNormalizationToBase X N) a) =
      algebraMap X.functionField N a := by
  have h : (gluedNormalizationFunctionFieldEquivAt X N U).toRingHom.comp
      (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom =
      algebraMap X.functionField N := by
    apply IsFractionRing.ringHom_ext (A := Γ(X, U.val))
    intro b
    have he : functionFieldMapOfDominant
        (normalizationChartToGlued X N U ≫ gluedNormalizationToBase X N) =
        functionFieldMapOfDominant
          (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.fromSpec) := by
      congr 1
      exact normalizationChartToGlued_comp_toBase X N U
    rw [functionFieldMapOfDominant_comp, functionFieldMapOfDominant_comp] at he
    have hc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he)
      (X.germToFunctionField U.val b)
    change functionFieldMapOfDominant (normalizationChartToGlued X N U)
      (functionFieldMapOfDominant (gluedNormalizationToBase X N) _) =
      functionFieldMapOfDominant (normalizedModelToBase Γ(X, U.val) N)
        (functionFieldMapOfDominant U.property.1.fromSpec _) at hc
    rw [functionFieldMapOfDominant_fromSpec_germ] at hc
    let r := CommRingCat.ofHom
      (algebraMap Γ(X, U.val) (normalizedCoordinateRing Γ(X, U.val) N))
    letI : IsDominant (Spec.map r) :=
      inferInstanceAs (IsDominant (normalizedModelToBase Γ(X, U.val) N))
    erw [functionFieldMapOfDominant_spec_algebraMap r b] at hc
    change affineNormalizationFunctionFieldEquiv X N U
      (functionFieldMapOfDominant (normalizationChartToGlued X N U)
        (functionFieldMapOfDominant (gluedNormalizationToBase X N) _)) = _
    erw [hc, affineNormalizationFunctionFieldEquiv_algebraMap X N U (r b)]
    rfl
  exact DFunLike.congr_fun h a

private def functionFieldComparisonChart : NonemptyAffineChart X :=
  Classical.choose (show ∃ U : NonemptyAffineChart X, True from by
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
    exact ⟨⟨U, hU, ⟨⟨genericPoint X, hx⟩⟩⟩, trivial⟩)

/-- The intrinsic field of the same glued normalization is the original finite
extension, as an algebra over the actual structural function-field map. -/
def gluedNormalizationFunctionFieldEquiv :
    letI : Algebra X.functionField (gluedNormalizationModel X N).functionField :=
      (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra
    (gluedNormalizationModel X N).functionField ≃ₐ[X.functionField] N := by
  letI : Algebra X.functionField (gluedNormalizationModel X N).functionField :=
    (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra
  exact
    { toRingEquiv := gluedNormalizationFunctionFieldEquivAt X N (functionFieldComparisonChart X)
      commutes' := gluedNormalizationFunctionFieldEquivAt_toBase X N (functionFieldComparisonChart X) }

/-- The canonical comparison agrees with every original chart computation. -/
theorem gluedNormalizationFunctionFieldEquiv_apply_chart
    (U : NonemptyAffineChart X) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquiv X N a =
      gluedNormalizationFunctionFieldEquivAt X N U a :=
  DFunLike.congr_fun
    (gluedNormalizationFunctionFieldEquivAt_eq X N (functionFieldComparisonChart X) U) a

end

end HodgeConjecture.CollisionFoundations
