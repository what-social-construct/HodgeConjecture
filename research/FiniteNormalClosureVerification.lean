import HodgeConjecture.Boundary
import Lean.Util.CollectAxioms

/-!
SP76 regressions for finite normalization in a marked normal closure.
Run with `lake env lean research/FiniteNormalClosureVerification.lean`.

The public boundary umbrella exposes normalization finiteness over a normal
Noetherian base and the one-model normalized-cover constructor. No perfect
base, Dedekind-domain hypothesis or second supplied affine algebra is used.
The existing structural morphism is finite by the proved ring finiteness.
Actual function-field tests retain the canonical generic-germ scalar action.
Every new public declaration has an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.NormalizationInertia
open HodgeConjecture.SchemeCycles

noncomputable section

universe u

section FiniteSeparableNormalization

variable {B K E : Type u} [CommRing B] [Field K] [Field E]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K E] [Algebra B E] [IsScalarTower B K E]
variable [IsIntegrallyClosed B] [IsNoetherianRing B]
variable [FiniteDimensional K E] [Algebra.IsSeparable K E]

example : Module.Finite B (normalizedCoordinateRing B E) := by
  fail_if_success have _ : PerfectField K := inferInstance
  fail_if_success have _ : IsDedekindDomain B := inferInstance
  exact normalizedCoordinateRing_finite_of_isSeparable (K := K)

example : IsNoetherianRing (normalizedCoordinateRing B E) := by
  letI := normalizedCoordinateRing_finite_of_isSeparable (B := B) (K := K) (E := E)
  exact IsNoetherianRing.of_finite B _

end FiniteSeparableNormalization

section MarkedNormalization

variable {B K L N : Type u} [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B N] [IsScalarTower B K N]
variable [IsIntegrallyClosed B] [IsNoetherianRing B] [Algebra.IsSeparable K L]
variable (D : NormalClosureData K L N)

-- Neither an action of B on L nor a separate separability instance for N
-- is a supplied input to this normal-closure specialization.
example : Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N)) := by
  fail_if_success have _ : PerfectField K := inferInstance
  fail_if_success have _ : IsDedekindDomain B := inferInstance
  exact normalClosureNormalizationRing_finite (B := B) D

-- This is the existing scheme morphism, not a new finite-map wrapper.
example : IsFinite (normalClosureNormalizationToBase (B := B) (N := N)) := by
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap B (NormalClosureNormalizationRing (B := B) (N := N))).Finite
  exact RingHom.finite_algebraMap.mpr (normalClosureNormalizationRing_finite (B := B) D)

end MarkedNormalization

section OneAffineModel

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [CommRing A] [Algebra B A] [Algebra A L]
variable [IsScalarTower B A L] [IsFractionRing A L] [IsIntegrallyClosed A]
variable [Module.Finite B A]
variable [IsIntegrallyClosed B] [IsNoetherianRing B] [Algebra.IsSeparable K L]
variable (D : NormalClosureData K L N)

example : (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D).normalClosure = D :=
  rfl

example : Module.Finite B (IntermediateNormalizationRing (B := B) (L := L)) :=
  (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D).finiteIntermediateModel

-- There is no S parameter or pre-existing normal-closure model in this context.
example : Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N)) := by
  fail_if_success have _ : Algebra.Etale B A := inferInstance
  exact (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D).finiteNormalClosureModel

example : IsOpenImmersion (intermediateToNormalization (B := B) (A := A) (E := L)) :=
  (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D).visibleOpen

example : IsFractionRing (NormalClosureNormalizationRing (B := B) (N := N)) N :=
  normalization_isFractionRing (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D)

example : IsIntegrallyClosed (NormalClosureNormalizationRing (B := B) (N := N)) :=
  normalization_isIntegrallyClosed (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D)

example : IsNoetherianRing (NormalClosureNormalizationRing (B := B) (N := N)) :=
  normalization_isNoetherianRing (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D)

example :
    intermediateToNormalization (B := B) (A := A) (E := L) ≫ normalizedModelToBase B L =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) :=
  intermediateToNormalization_comp_toBase (B := B) (A := A) (E := L)

example (I : Subgroup D.galoisGroup) (hI : I ≠ ⊥) :
    fixedMovingBoundaryIdeal
      (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D) I = ⊤ :=
  fixedMovingBoundaryIdeal_eq_top_of_surjective _
    (intermediateToNormalization_base_surjective (B := B) (A := A) (E := L)) I hI

example : ConjugateBoundarySeparation
    (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D) := by
  fail_if_success have _ : PerfectField K := inferInstance
  fail_if_success have _ : IsDedekindDomain B := inferInstance
  fail_if_success have _ : Algebra.Etale B A := inferInstance
  exact conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModel D

end OneAffineModel

-- Construct the marked datum as well as the cover, with one genuine field
-- affine model and no supplied algebra in its normal closure.
example (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ C : NormalizedCover (B := K) (K := K) (L := L)
      (N := IntermediateField.normalClosure K L (AlgebraicClosure L))
      (Spec (.of L)) (intermediateToNormalization (B := K) (A := L) (E := L)),
      C.normalClosure = NormalClosureData.ofAlgebraicClosure K L ∧
        ConjugateBoundarySeparation C := by
  let D := NormalClosureData.ofAlgebraicClosure K L
  refine ⟨normalizedCoverOfFiniteNormalAffineModel (B := K) (A := L) D, rfl, ?_⟩
  exact conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModel D

section ActualGenericExtension

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
variable [IsIntegrallyClosed Γ(X, U)] [IsNoetherianRing Γ(X, U)]

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    Module.Finite Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : IsDedekindDomain Γ(X, U) := inferInstance
  exact functionFieldNormalClosure_normalization_finite p U hU

example [IsEtale p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    Module.Finite Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) :=
  functionFieldNormalClosure_normalization_finite p U hU

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    IsFinite (normalClosureNormalizationToBase (B := Γ(X, U)) (N := N)) := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) N)).Finite
  exact RingHom.finite_algebraMap.mpr (functionFieldNormalClosure_normalization_finite p U hU)

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    IsNoetherianRing (normalizedCoordinateRing Γ(X, U) N) := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI := functionFieldNormalClosure_normalization_finite p U hU
  exact IsNoetherianRing.of_finite Γ(X, U) _

example (a : Γ(X, U)) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    algebraMap Γ(X, U) N a =
      algebraMap X.functionField N ((X.germToFunctionField U) a) := rfl

-- This package uses the literal whole preimage and existing normalization
-- isomorphism. Its marking, both finite-model fields, and base triangle agree.
example [FormallyUnramified p]
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    let C : NormalizedCover (B := Γ(X, U)) (K := X.functionField)
      (L := Y.functionField) (N := N) (p ⁻¹ᵁ U).toScheme
      (finiteAffinePreimageNormalizationIso p U hU hNormal).hom :=
        finiteAffinePreimageNormalizedCover p U hU hNormal
    C.normalClosure = functionFieldNormalClosureData p ∧
      Module.Finite Γ(X, U) (IntermediateNormalizationRing (B := Γ(X, U)) (L := Y.functionField)) ∧
      Module.Finite Γ(X, U) (NormalClosureNormalizationRing (B := Γ(X, U)) (N := N)) ∧
      IsOpenImmersion (finiteAffinePreimageNormalizationIso p U hU hNormal).hom ∧
      (finiteAffinePreimageNormalizationIso p U hU hNormal).hom ≫
          normalizedModelToBase Γ(X, U) Y.functionField ≫ hU.fromSpec =
        (p ⁻¹ᵁ U).ι ≫ p := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  let C := finiteAffinePreimageNormalizedCover p U hU hNormal
  exact ⟨rfl, C.finiteIntermediateModel, C.finiteNormalClosureModel, C.visibleOpen,
    finiteAffinePreimageNormalizationIso_hom_comp_toBase p U hU hNormal⟩

example [FormallyUnramified p]
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
    ConjugateBoundarySeparation (finiteAffinePreimageNormalizedCover p U hU hNormal) := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover p U hU hNormal

example [IsEtale p]
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
    ConjugateBoundarySeparation (finiteAffinePreimageNormalizedCover p U hU hNormal) :=
  conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover p U hU hNormal

end ActualGenericExtension

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.normalizedCoordinateRing_finite_of_isSeparable,
      `HodgeConjecture.NormalizationInertia.normalClosureNormalizationRing_finite,
      `HodgeConjecture.NormalizationInertia.normalizedCoverOfFiniteNormalAffineModel,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModel,
      `HodgeConjecture.CollisionFoundations.functionFieldNormalClosure_normalization_finite,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimageNormalizedCover,
      `HodgeConjecture.CollisionFoundations.conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
