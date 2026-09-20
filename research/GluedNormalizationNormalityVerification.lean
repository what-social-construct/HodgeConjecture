import HodgeConjecture.Boundary.Normalization.GluedNormalizationNormality
import HodgeConjecture.Boundary.Normalization.GluedNormalizationChart
import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import Lean.Util.CollectAxioms

/-!
SP91 regressions for normal local rings of the original glued normalization.
Run with `lake env lean research/GluedNormalizationNormalityVerification.lean`.

The affine assertions allow any commutative base ring mapping to a field.
The global assertions allow any extension of the original function field.
Normality is tested as domain and integrally closed actual stalks, including
on the original chart images and open restrictions. No global `IsIntegral`
instance or identification of the ambient field with the fraction field of
the integral closure is assumed. The actual normal-closure specialization
retains the original field marking and generic-germ scalars.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles

noncomputable section

universe u

section ArbitraryAffineBase

variable (B N : Type u) [CommRing B] [Field N] [Algebra B N]

example : IsDomain (normalizedCoordinateRing B N) := inferInstance

example : IsIntegrallyClosed (normalizedCoordinateRing B N) := by
  fail_if_success have _ : IsDomain B := inferInstance
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : IsFractionRing (normalizedCoordinateRing B N) N := inferInstance
  exact normalizedCoordinateRing_isIntegrallyClosed B N

example : IsDomain (normalizedCoordinateRing B N) ∧
    IsIntegrallyClosed (normalizedCoordinateRing B N) :=
  ⟨inferInstance, normalizedCoordinateRing_isIntegrallyClosed B N⟩

example : Nonempty (FractionRing (normalizedCoordinateRing B N) →ₐ[
    normalizedCoordinateRing B N] N) := by
  exact ⟨IsFractionRing.liftAlgHom (g := Algebra.ofId (normalizedCoordinateRing B N) N)
    (IsIntegralClosure.algebraMap_injective (normalizedCoordinateRing B N) B N)⟩

example (z : normalizedAffineModel B N) :
    IsDomain ((normalizedAffineModel B N).presheaf.stalk z) := by
  letI : IsIntegral (normalizedAffineModel B N) := by
    unfold normalizedAffineModel
    infer_instance
  infer_instance

example (z : normalizedAffineModel B N) :
    IsIntegrallyClosed ((normalizedAffineModel B N).presheaf.stalk z) := by
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : Algebra.IsIntegral B N := inferInstance
  exact normalizedAffineModel_stalk_isIntegrallyClosed B N z

example (z : normalizedAffineModel B N) :
    IsDomain ((normalizedAffineModel B N).presheaf.stalk z) ∧
      IsIntegrallyClosed ((normalizedAffineModel B N).presheaf.stalk z) := by
  letI : IsIntegral (normalizedAffineModel B N) := by
    unfold normalizedAffineModel
    infer_instance
  exact ⟨inferInstance, normalizedAffineModel_stalk_isIntegrallyClosed B N z⟩

end ArbitraryAffineBase

section ArbitraryFunctionFieldExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance normalityVerificationAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example (U : NonemptyAffineChart X) :
    IsIntegrallyClosed (normalizedCoordinateRing Γ(X, U.val) N) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  exact normalizedCoordinateRing_isIntegrallyClosed Γ(X, U.val) N

example (U : NonemptyAffineChart X) (z : (affineNormalizationDiagram X N).obj U) :
    IsIntegrallyClosed (((affineNormalizationDiagram X N).obj U).presheaf.stalk z) :=
  normalizedAffineModel_stalk_isIntegrallyClosed Γ(X, U.val) N z

example (U : NonemptyAffineChart X) (z : (affineNormalizationDiagram X N).obj U) :
    IsIso ((normalizationChartToGlued X N U).stalkMap z) := inferInstance

example (z : gluedNormalizationModel X N) :
    IsDomain ((gluedNormalizationModel X N).presheaf.stalk z) := by
  fail_if_success have _ : IsIntegral (gluedNormalizationModel X N) := inferInstance
  exact gluedNormalizationModel_stalk_isDomain X N z

example (z : gluedNormalizationModel X N) :
    IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk z) := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsAlgebraic X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField N := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  exact gluedNormalizationModel_stalk_isIntegrallyClosed X N z

example (z : gluedNormalizationModel X N) :
    IsDomain ((gluedNormalizationModel X N).presheaf.stalk z) ∧
      IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk z) :=
  ⟨gluedNormalizationModel_stalk_isDomain X N z,
    gluedNormalizationModel_stalk_isIntegrallyClosed X N z⟩

example (U : NonemptyAffineChart X) (z : (affineNormalizationDiagram X N).obj U) :
    IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk
      ((normalizationChartToGlued X N U).base z)) :=
  gluedNormalizationModel_stalk_isIntegrallyClosed X N _

example (U : NonemptyAffineChart X) (z : (affineNormalizationDiagram X N).obj U) :
    IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk
      ((normalizationChartToGlued X N U).base z)) := by
  letI : IsIntegrallyClosed (((affineNormalizationDiagram X N).obj U).presheaf.stalk z) :=
    normalizedAffineModel_stalk_isIntegrallyClosed Γ(X, U.val) N z
  exact IsIntegrallyClosed.of_equiv
    (asIso ((normalizationChartToGlued X N U).stalkMap z)).symm.commRingCatIsoToRingEquiv

example (V : (gluedNormalizationModel X N).Opens) (z : V) :
    IsDomain (V.toScheme.presheaf.stalk z) := by
  letI := gluedNormalizationModel_stalk_isDomain X N z.val
  exact (V.stalkIso z).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

example (V : (gluedNormalizationModel X N).Opens) (z : V) :
    IsIntegrallyClosed (V.toScheme.presheaf.stalk z) := by
  letI : IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk (V.ι.base z)) :=
    gluedNormalizationModel_stalk_isIntegrallyClosed X N _
  exact IsIntegrallyClosed.of_equiv
    (asIso (V.ι.stalkMap z)).commRingCatIsoToRingEquiv

example (V : (gluedNormalizationModel X N).Opens) [Nonempty V] (z : V) :
    IsDomain (V.toScheme.presheaf.stalk z) ∧
      IsIntegrallyClosed (V.toScheme.presheaf.stalk z) := by
  fail_if_success have _ : IsIntegral (gluedNormalizationModel X N) := inferInstance
  letI := gluedNormalizationModel_stalk_isDomain X N z.val
  letI := gluedNormalizationModel_stalk_isIntegrallyClosed X N z.val
  exact ⟨(V.stalkIso z).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _,
    IsIntegrallyClosed.of_equiv (V.stalkIso z).symm.commRingCatIsoToRingEquiv⟩

example (U : NonemptyAffineChart X)
    (z : (gluedNormalizationToBase X N) ⁻¹ᵁ U.val) :
    IsIntegrallyClosed
      (((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).toScheme.presheaf.stalk z) := by
  letI := gluedNormalizationModel_stalk_isIntegrallyClosed X N z.val
  exact IsIntegrallyClosed.of_equiv
    (((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).stalkIso z).symm.commRingCatIsoToRingEquiv

end ArbitraryFunctionFieldExtension

section OriginalMarkedNormalClosure

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U.val) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
    algebraMap Γ(X, U.val) Nₚ b =
      algebraMap X.functionField Nₚ ((X.germToFunctionField U.val).hom b) := rfl

example (a : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding a : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) a :=
  functionFieldNormalClosureData_embedding_apply p a

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ z : gluedNormalizationModel X Nₚ,
      IsDomain ((gluedNormalizationModel X Nₚ).presheaf.stalk z) ∧
        IsIntegrallyClosed ((gluedNormalizationModel X Nₚ).presheaf.stalk z) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  fail_if_success
    have _ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun _ => inferInstance
  intro z
  exact ⟨gluedNormalizationModel_stalk_isDomain X Nₚ z,
    gluedNormalizationModel_stalk_isIntegrallyClosed X Nₚ z⟩

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ z : (affineNormalizationDiagram X Nₚ).obj U,
      IsIntegrallyClosed (((affineNormalizationDiagram X Nₚ).obj U).presheaf.stalk z) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U.val) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
  intro z
  exact normalizedAffineModel_stalk_isIntegrallyClosed Γ(X, U.val) Nₚ z

end OriginalMarkedNormalClosure

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.normalizedCoordinateRing_isIntegrallyClosed,
    `HodgeConjecture.CollisionFoundations.normalizedAffineModel_stalk_isIntegrallyClosed,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationModel_stalk_isDomain,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationModel_stalk_isIntegrallyClosed]
  unless declarations.length == 4 do
    throwError "Expected exactly 4 SP91 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP91 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    let actual := state.axioms.toList
    unless actual.length == permitted.length do
      throwError "Expected exactly the standard three axioms in {declaration}, got {actual}"
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS exact standard-three axiom boundary: {declaration}; {actual}"
  logInfo "PASS SP91 audit registry: 4 distinct public declarations"
