import HodgeConjecture.Boundary.Normalization.GluedNormalizationFunctionFieldAction
import HodgeConjecture.Boundary.Normalization.GluedNormalClosureFunctionField
import Lean.Util.CollectAxioms

/-!
SP93 focused checks for the original normalization's function field.
Run with `lake env lean research/GluedNormalizationFunctionFieldVerification.lean`.

The finite-extension comparison uses the actual generic-stalk maps, agrees
on every original chart, and retains the inverse-ring action convention.
The marked specialization preserves the original normal-closure embedding
under finite dominance and normal stalks of the upstairs scheme only.
These tests do not assert reconstruction of all deck transformations.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles

noncomputable section

universe u

#check openImmersion_isDominant_of_nonempty
#check functionFieldMapOfDominant_spec_algebraMap
#check functionFieldMapOfDominant_fromSpec_germ
#check specMap_isDominant_of_injective
#check affineNormalizationFunctionFieldEquiv
#check affineNormalizationFunctionFieldEquiv_algebraMap
#check gluedNormalizationFunctionFieldEquivAt
#check gluedNormalizationFunctionFieldEquivAt_apply_chart
#check gluedNormalizationFunctionFieldEquivAt_restriction
#check gluedNormalizationFunctionFieldEquivAt_eq
#check gluedNormalizationFunctionFieldEquivAt_toBase
#check gluedNormalizationFunctionFieldEquiv
#check gluedNormalizationFunctionFieldEquiv_apply_chart
#check affineNormalizationFunctionFieldEquiv_automorphism
#check gluedNormalizationFunctionFieldEquivAt_automorphism
#check gluedNormalizationFunctionFieldEquiv_automorphism
#check gluedNormalizationDeckAction_injective
#check gluedNormalClosureFunctionFieldEquivAt_toCover
#check gluedNormalClosureFunctionFieldEquiv_toCover

section GenericStalkCoordinates

example {A B : Scheme.{u}} [Nonempty A] [IrreducibleSpace B]
    (j : A ⟶ B) [IsOpenImmersion j] : IsDominant j :=
  openImmersion_isDominant_of_nonempty j

example {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : Function.Injective f) :
    IsDominant (Spec.map f) :=
  specMap_isDominant_of_injective f hf

example {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (f : R ⟶ S) [IsDominant (Spec.map f)] (r : R) :
    functionFieldMapOfDominant (Spec.map f)
        (algebraMap R (Spec R).functionField r) =
      algebraMap S (Spec S).functionField (f r) :=
  functionFieldMapOfDominant_spec_algebraMap f r

example {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (b : Γ(X, U)) :
    functionFieldMapOfDominant hU.fromSpec (X.germToFunctionField U b) =
      algebraMap Γ(X, U) (Spec Γ(X, U)).functionField b :=
  functionFieldMapOfDominant_fromSpec_germ U hU b

-- Integrality for arbitrary ambient extensions has not silently acquired
-- the finite-dimensional premise needed by the function-field comparison.
example {X : Scheme.{u}} [IsIntegral X] (N : Type u) [Field N]
    [Algebra X.functionField N] : IsIntegral (gluedNormalizationModel X N) := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsAlgebraic X.functionField N := inferInstance
  infer_instance

end GenericStalkCoordinates

section FiniteAmbientExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable [FiniteDimensional X.functionField N]

local instance verificationAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

local instance verificationChartIntegral (U : NonemptyAffineChart X) :
    IsIntegral ((affineNormalizationDiagram X N).obj U) := by
  change IsIntegral (normalizedAffineModel Γ(X, U.val) N)
  unfold normalizedAffineModel
  infer_instance

local instance verificationChartFieldAlgebra (U : NonemptyAffineChart X) :
    Algebra (normalizedCoordinateRing Γ(X, U.val) N)
      ((affineNormalizationDiagram X N).obj U).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (.of (normalizedCoordinateRing Γ(X, U.val) N))

local instance : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance : Algebra X.functionField (gluedNormalizationModel X N).functionField :=
  (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra

example (U : NonemptyAffineChart X) :
    ((affineNormalizationDiagram X N).obj U).functionField ≃+* N :=
  affineNormalizationFunctionFieldEquiv X N U

example (U : NonemptyAffineChart X) (t : normalizedCoordinateRing Γ(X, U.val) N) :
    affineNormalizationFunctionFieldEquiv X N U
        (algebraMap (normalizedCoordinateRing Γ(X, U.val) N)
          ((affineNormalizationDiagram X N).obj U).functionField t) = (t : N) :=
  affineNormalizationFunctionFieldEquiv_algebraMap X N U t

example (U : NonemptyAffineChart X) :
    (gluedNormalizationModel X N).functionField ≃+* N :=
  gluedNormalizationFunctionFieldEquivAt X N U

example (U : NonemptyAffineChart X) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U a =
      affineNormalizationFunctionFieldEquiv X N U
        (functionFieldMapOfDominant (normalizationChartToGlued X N U) a) :=
  gluedNormalizationFunctionFieldEquivAt_apply_chart X N U a

example {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    gluedNormalizationFunctionFieldEquivAt X N U =
      gluedNormalizationFunctionFieldEquivAt X N V :=
  gluedNormalizationFunctionFieldEquivAt_restriction X N f

example (U V : NonemptyAffineChart X) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U a =
      gluedNormalizationFunctionFieldEquivAt X N V a :=
  DFunLike.congr_fun (gluedNormalizationFunctionFieldEquivAt_eq X N U V) a

example (U : NonemptyAffineChart X) (a : X.functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U
        (functionFieldMapOfDominant (gluedNormalizationToBase X N) a) =
      algebraMap X.functionField N a :=
  gluedNormalizationFunctionFieldEquivAt_toBase X N U a

example : (gluedNormalizationModel X N).functionField ≃ₐ[X.functionField] N :=
  gluedNormalizationFunctionFieldEquiv X N

example (U : NonemptyAffineChart X) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquiv X N a =
      gluedNormalizationFunctionFieldEquivAt X N U a :=
  gluedNormalizationFunctionFieldEquiv_apply_chart X N U a

example (a : X.functionField) :
    gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant (gluedNormalizationToBase X N) a) =
      algebraMap X.functionField N a :=
  (gluedNormalizationFunctionFieldEquiv X N).commutes a

example : Function.Surjective (gluedNormalizationFunctionFieldEquiv X N) :=
  (gluedNormalizationFunctionFieldEquiv X N).surjective

example : Function.Injective (gluedNormalizationFunctionFieldEquiv X N) :=
  (gluedNormalizationFunctionFieldEquiv X N).injective

example (a : (gluedNormalizationModel X N).functionField) :
    (gluedNormalizationFunctionFieldEquiv X N).symm
        (gluedNormalizationFunctionFieldEquiv X N a) = a :=
  (gluedNormalizationFunctionFieldEquiv X N).symm_apply_apply a

example (U : NonemptyAffineChart X) (t : normalizedCoordinateRing Γ(X, U.val) N) :
    gluedNormalizationFunctionFieldEquivAt X N U
        ((functionFieldEquivOfOpenImmersion (normalizationChartToGlued X N U)).symm
          (algebraMap (normalizedCoordinateRing Γ(X, U.val) N)
            ((affineNormalizationDiagram X N).obj U).functionField t)) = (t : N) := by
  change affineNormalizationFunctionFieldEquiv X N U
    ((functionFieldEquivOfOpenImmersion (normalizationChartToGlued X N U))
      ((functionFieldEquivOfOpenImmersion (normalizationChartToGlued X N U)).symm _)) = _
  rw [RingEquiv.apply_symm_apply]
  exact affineNormalizationFunctionFieldEquiv_algebraMap X N U t

example : (gluedNormalizationModel X N).functionField ≃ₐ[X.functionField] N := by
  fail_if_success have _ : Algebra.IsSeparable X.functionField N := inferInstance
  fail_if_success have _ : IsGalois X.functionField N := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact gluedNormalizationFunctionFieldEquiv X N

example (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X)
    (a : ((affineNormalizationDiagram X N).obj U).functionField) :
    affineNormalizationFunctionFieldEquiv X N U
        (functionFieldMapOfDominant (affineNormalizationChartAutomorphism X N σ U).hom a) =
      σ.symm (affineNormalizationFunctionFieldEquiv X N U a) :=
  affineNormalizationFunctionFieldEquiv_automorphism X N σ U a

example (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X)
    (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U
        (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom a) =
      σ.symm (gluedNormalizationFunctionFieldEquivAt X N U a) :=
  gluedNormalizationFunctionFieldEquivAt_automorphism X N σ U a

example (σ : N ≃ₐ[X.functionField] N) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom a) =
      σ.symm (gluedNormalizationFunctionFieldEquiv X N a) :=
  gluedNormalizationFunctionFieldEquiv_automorphism X N σ a

example : Function.Injective (gluedNormalizationDeckAction X N) :=
  gluedNormalizationDeckAction_injective X N

example (σ : N ≃ₐ[X.functionField] N) (x : N) :
    gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom
          ((gluedNormalizationFunctionFieldEquiv X N).symm x)) = σ.symm x := by
  rw [gluedNormalizationFunctionFieldEquiv_automorphism, AlgEquiv.apply_symm_apply]

example (σ τ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationDeckAction X N σ = gluedNormalizationDeckAction X N τ ↔ σ = τ :=
  (gluedNormalizationDeckAction_injective X N).eq_iff

example (σ τ : N ≃ₐ[X.functionField] N)
    (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N (σ * τ)).hom a) =
      τ.symm (σ.symm (gluedNormalizationFunctionFieldEquiv X N a)) := by
  rw [gluedNormalizationFunctionFieldEquiv_automorphism]
  rfl

end FiniteAmbientExtension

section OriginalMarkedNormalClosure

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example (U : NonemptyAffineChart X) (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    gluedNormalizationFunctionFieldEquivAt X Nₚ U
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) =
      (functionFieldNormalClosureData p).embedding c :=
  gluedNormalClosureFunctionFieldEquivAt_toCover p hY U c

example (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) =
      (functionFieldNormalClosureData p).embedding c :=
  gluedNormalClosureFunctionFieldEquiv_toCover p hY c

example (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    (gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) :
          AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  rw [gluedNormalClosureFunctionFieldEquiv_toCover]
  exact functionFieldNormalClosureData_embedding_apply p c

example (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding c : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) c :=
  functionFieldNormalClosureData_embedding_apply p c

example (a : X.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY)
          (functionFieldMapOfDominant p a)) = algebraMap X.functionField Nₚ a := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  rw [gluedNormalClosureFunctionFieldEquiv_toCover]
  exact (functionFieldNormalClosureData p).embedding.commutes a

example (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) =
      (functionFieldNormalClosureData p).embedding c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField Y.functionField := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact gluedNormalClosureFunctionFieldEquiv_toCover p hY c

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    Function.Injective (gluedNormalizationDeckAction X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  exact gluedNormalizationDeckAction_injective X Nₚ

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ (σ : Nₚ ≃ₐ[X.functionField] Nₚ)
      (a : (gluedNormalizationModel X Nₚ).functionField),
      gluedNormalizationFunctionFieldEquiv X Nₚ
          (functionFieldMapOfDominant (gluedNormalizationAutomorphism X Nₚ σ).hom a) =
        σ.symm (gluedNormalizationFunctionFieldEquiv X Nₚ a) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro σ a
  exact gluedNormalizationFunctionFieldEquiv_automorphism X Nₚ σ a

end OriginalMarkedNormalClosure

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCycles.openImmersion_isDominant_of_nonempty,
    `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_spec_algebraMap,
    `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_fromSpec_germ,
    `HodgeConjecture.SchemeCycles.specMap_isDominant_of_injective,
    `HodgeConjecture.CollisionFoundations.affineNormalizationFunctionFieldEquiv,
    `HodgeConjecture.CollisionFoundations.affineNormalizationFunctionFieldEquiv_algebraMap,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquivAt,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquivAt_apply_chart,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquivAt_restriction,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquivAt_eq,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquivAt_toBase,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquiv,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquiv_apply_chart,
    `HodgeConjecture.CollisionFoundations.affineNormalizationFunctionFieldEquiv_automorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquivAt_automorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationFunctionFieldEquiv_automorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckAction_injective,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureFunctionFieldEquivAt_toCover,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureFunctionFieldEquiv_toCover]
  unless declarations.length == 19 do
    throwError "Expected exactly 19 SP93 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP93 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    let actual := state.axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP93 audit registry: 19 distinct public declarations"
