module

import HodgeConjecture.Boundary.Normalization.GluedNormalizationIntegrality
import HodgeConjecture.Boundary.Normalization.GluedNormalizationChart
import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP92 regressions for integrality of the original glued normalization.
Run with `lake env lean research/GluedNormalizationIntegralityVerification.lean`.

The original charts overlap and the same global scheme is reduced,
irreducible, and integral for an arbitrary ambient function-field extension.
Consumers check section domains, actual stalks, nonempty open restrictions,
and the now available intrinsic function field without identifying it with
the ambient field. The marked specialization retains the original generic
germs and field embedding without a normal-stalk premise on either scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles

noncomputable section

universe u

section ArbitraryFunctionFieldExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance integralityVerificationAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example (U : NonemptyAffineChart X) :
    IsIntegral ((affineNormalizationDiagram X N).obj U) := by
  change IsIntegral (normalizedAffineModel Γ(X, U.val) N)
  unfold normalizedAffineModel
  infer_instance

example (U V : NonemptyAffineChart X) :
    (Set.range (normalizationChartToGlued X N U).base ∩
      Set.range (normalizationChartToGlued X N V).base).Nonempty :=
  normalizationChartToGlued_range_inter_nonempty X N U V

example (U V : NonemptyAffineChart X) :
    ∃ (a : (affineNormalizationDiagram X N).obj U)
      (b : (affineNormalizationDiagram X N).obj V),
      (normalizationChartToGlued X N U).base a =
        (normalizationChartToGlued X N V).base b := by
  obtain ⟨z, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    normalizationChartToGlued_range_inter_nonempty X N U V
  exact ⟨a, b, ha.trans hb.symm⟩

example (U V : NonemptyAffineChart X) :
    ((gluedNormalizationToBase X N).base ⁻¹' (U.val : Set X) ∩
      (gluedNormalizationToBase X N).base ⁻¹' (V.val : Set X)).Nonempty := by
  rw [← normalizationChartToGlued_range X N U, ← normalizationChartToGlued_range X N V]
  exact normalizationChartToGlued_range_inter_nonempty X N U V

example : IsReduced (gluedNormalizationModel X N) :=
  gluedNormalizationModel_isReduced X N

example : IsReduced (gluedNormalizationModel X N) := inferInstance

example : IrreducibleSpace (gluedNormalizationModel X N) :=
  gluedNormalizationModel_irreducibleSpace X N

example : Nonempty (gluedNormalizationModel X N) := inferInstance

example : IsIntegral (gluedNormalizationModel X N) := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsAlgebraic X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField N := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  infer_instance

example : IsDomain Γ(gluedNormalizationModel X N, ⊤) := inferInstance

example (V : (gluedNormalizationModel X N).Opens) [Nonempty V] :
    IsDomain Γ(gluedNormalizationModel X N, V) := inferInstance

example (V : (gluedNormalizationModel X N).Opens) [Nonempty V] :
    IsIntegral V.toScheme :=
  isIntegral_of_isOpenImmersion V.ι

example (z : gluedNormalizationModel X N) :
    IsDomain ((gluedNormalizationModel X N).presheaf.stalk z) := inferInstance

example (z : gluedNormalizationModel X N) :
    IsDomain ((gluedNormalizationModel X N).presheaf.stalk z) ∧
      IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk z) :=
  ⟨inferInstance, gluedNormalizationModel_stalk_isIntegrallyClosed X N z⟩

example (V : (gluedNormalizationModel X N).Opens) [Nonempty V] :
    Function.Injective ((gluedNormalizationModel X N).germToFunctionField V) :=
  (gluedNormalizationModel X N).germToFunctionField_injective V

example (z : gluedNormalizationModel X N) :
    Specializes (genericPoint (gluedNormalizationModel X N)) z :=
  genericPoint_specializes z

example : Field (gluedNormalizationModel X N).functionField := inferInstance

example (A B : (gluedNormalizationModel X N).Opens) [hA : Nonempty A] [hB : Nonempty B] :
    ((A : Set (gluedNormalizationModel X N)) ∩ B).Nonempty :=
  nonempty_preirreducible_inter A.isOpen B.isOpen
    ⟨(Classical.choice hA).val, (Classical.choice hA).property⟩
    ⟨(Classical.choice hB).val, (Classical.choice hB).property⟩

example : IsIntegral (gluedNormalizationModel X X.functionField) := inferInstance

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
    IsIntegral (gluedNormalizationModel X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  fail_if_success
    have _ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun _ => inferInstance
  infer_instance

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ z : gluedNormalizationModel X Nₚ,
      IsDomain ((gluedNormalizationModel X Nₚ).presheaf.stalk z) ∧
        IsIntegrallyClosed ((gluedNormalizationModel X Nₚ).presheaf.stalk z) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro z
  exact ⟨inferInstance, gluedNormalizationModel_stalk_isIntegrallyClosed X Nₚ z⟩

end OriginalMarkedNormalClosure

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_range_inter_nonempty,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationModel_isReduced,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationModel_irreducibleSpace,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationModel_isIntegral]
  unless declarations.length == 4 do
    throwError "Expected exactly 4 SP92 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP92 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    unless actual.length == permitted.length do
      throwError "Expected exactly the standard three axioms in {declaration}, got {actual}"
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS exact standard-three axiom boundary: {declaration}; {actual}"
  logInfo "PASS SP92 audit registry: 4 distinct public declarations"
