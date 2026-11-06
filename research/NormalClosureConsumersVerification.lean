module

import HodgeConjecture.Boundary
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP75 regressions for the consumers of constructed marked normal closures.
Run with `lake env lean research/NormalClosureConsumersVerification.lean`.

Fixed-field, invariant-ring and tensor-splitting consumers use separability
of the marked extension. Core-freeness, fully visible boundary separation
and the abstract inertia contradiction need neither separability nor a
perfect base. Actual finite formally unramified morphisms provide the needed
separability for their constructed normal closures. The old perfect-field
Galois theorem remains a compatibility wrapper. All 29 changed declarations
have an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.SchemeCycles HodgeConjecture.CollisionFoundations
open HodgeConjecture.NormalizationInertia
open scoped TensorProduct

noncomputable section

universe uK uL uN u

section CoreConsumers

variable {K : Type uK} {L : Type uL} {N : Type uN}
variable [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
variable (D : NormalClosureData K L N)

example : D.intermediateFixingSubgroup.normalCore = ⊥ := by
  fail_if_success have _ : PerfectField K := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact D.intermediateFixingSubgroup_normalCore_eq_bot

-- The retained wrapper still handles a perfect base without asking callers
-- to install the package's finite-dimensional instances themselves.
example [PerfectField K] : IsGalois K N := D.isGalois

example [PerfectField K] :
    IntermediateField.fixedField D.intermediateFixingSubgroup = D.intermediateField := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact D.fixedField_intermediateFixingSubgroup

variable [Algebra.IsSeparable K L]

example : Algebra.IsSeparable K N := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.isSeparable

example : IsGalois K N := D.isGalois_of_isSeparable

example :
    IntermediateField.fixedField D.intermediateFixingSubgroup = D.intermediateField := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.fixedField_intermediateFixingSubgroup

example : Function.Bijective D.normalClosureTensorToGenericSheets :=
  D.normalClosureTensorToGenericSheets_bijective

example : N ⊗[K] L ≃ₐ[N] GenericSheetAlgebra N D.intermediateFixingSubgroup :=
  D.normalClosureTensorGenericSheetsEquiv

example :
    D.normalClosureBaseSheetAugmentation.comp
        D.normalClosureTensorGenericSheetsEquiv.toAlgHom =
      D.normalClosureTensorDiagonal :=
  D.normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv

end CoreConsumers

section InvariantRings

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [Algebra.IsSeparable K L] (D : NormalClosureData K L N)

example : IntermediateNormalizationRing (B := B) (L := L) ≃ₐ[B]
    FixedSubgroupNormalizationRing (B := B) D.intermediateFixingSubgroup := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact intermediateNormalizationEquivFixedRing (B := B) D

example (x : IntermediateNormalizationRing (B := B) (L := L)) :
    (((intermediateNormalizationEquivFixedRing (B := B) D x :
        FixedSubgroupNormalizationRing (B := B) D.intermediateFixingSubgroup) :
      NormalClosureNormalizationRing (B := B) (N := N)) : N) = D.embedding (x : L) :=
  intermediateNormalizationEquivFixedRing_coe D x

example [IsFractionRing B K] [IsIntegrallyClosed B] :
    B ≃ₐ[B] FullInvariantNormalizationRing (B := B) (K := K) (N := N) :=
  baseEquivFullInvariantNormalizationRing (B := B) D

end InvariantRings

section BoundaryWithoutSeparability

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)

example (hVisible : Function.Surjective j.base)
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I = ⊤ := by
  fail_if_success have _ : PerfectField K := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact movingBoundaryIdeal_eq_top_of_surjective C hVisible I hI

example (hVisible : Function.Surjective j.base)
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    fixedMovingBoundaryIdeal C I = ⊤ :=
  fixedMovingBoundaryIdeal_eq_top_of_surjective C hVisible I hI

example (hVisible : Function.Surjective j.base) : ConjugateBoundarySeparation C := by
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact conjugateBoundarySeparation_of_surjective C hVisible

example (D : Diagram C) (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    ∃ q : D.sheetClasses E, 1 < D.inertiaIndex E q := by
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact D.exists_one_lt_inertiaIndex E

example (D : Diagram C) (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    IsEmpty (RamifiedCodimensionOnePoint (B := B) (N := N)) :=
  D.ramifiedCodimensionOnePoint_isEmpty hBoundary hNoHidden

example (D : Diagram C) (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    NoCodimensionOneRamification (B := B) (N := N) :=
  D.noCodimensionOneRamification hBoundary hNoHidden

example [IsNoetherianRing B] (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (hFormal : FormallyUnramified
      (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia)
    (selected : Set (GaloisSheets C.normalClosure.intermediateFixingSubgroup)) :
    ∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
      InertiaSaturated (inertiaGroupAt K (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup selected := by
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact D.forall_inertiaSaturated_of_formallyUnramified R hFormal hNoHidden selected

example {A S : Type u} [CommRing A] [CommRing S]
    [Algebra B A] [Algebra A L] [IsScalarTower B A L]
    [IsFractionRing A L] [IsIntegrallyClosed A] [Module.Finite B A]
    [Algebra B S] [Algebra S N] [IsScalarTower B S N]
    [IsFractionRing S N] [IsIntegrallyClosed S] [Module.Finite B S]
    (D : NormalClosureData K L N) :
    ConjugateBoundarySeparation
      (normalizedCoverOfFiniteNormalAffineModels (B := B) (A := A) (S := S) D) := by
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels D

end BoundaryWithoutSeparability

section ActualGenericExtension

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureData p).intermediateFixingSubgroup.normalCore = ⊥ := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField Y.functionField := inferInstance
  exact (functionFieldNormalClosureData p).intermediateFixingSubgroup_normalCore_eq_bot

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    IntermediateField.fixedField (functionFieldNormalClosureData p).intermediateFixingSubgroup =
      (functionFieldNormalClosureData p).intermediateField := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact (functionFieldNormalClosureData p).fixedField_intermediateFixingSubgroup

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Function.Bijective (functionFieldNormalClosureData p).normalClosureTensorToGenericSheets := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  exact (functionFieldNormalClosureData p).normalClosureTensorToGenericSheets_bijective

example [Etale p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    letI := functionFieldMapOfDominant_isSeparable p
    (functionFieldNormalClosureData p).normalClosureBaseSheetAugmentation.comp
        (functionFieldNormalClosureData p).normalClosureTensorGenericSheetsEquiv.toAlgHom =
      (functionFieldNormalClosureData p).normalClosureTensorDiagonal := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  exact (functionFieldNormalClosureData p).normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv

end ActualGenericExtension

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.NormalClosureData.isSeparable,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.isGalois_of_isSeparable,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.isGalois,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.fixedField_intermediateFixingSubgroup,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.intermediateFixingSubgroup_normalCore_eq_bot,
      `HodgeConjecture.NormalizationInertia.intermediateNormalizationEquivFixedRing,
      `HodgeConjecture.NormalizationInertia.intermediateNormalizationEquivFixedRing_coe,
      `HodgeConjecture.NormalizationInertia.baseEquivFullInvariantNormalizationRing,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorToGenericSheets_bijective,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorGenericSheetsEquiv,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv,
      `HodgeConjecture.NormalizationInertia.movingBoundaryIdeal_eq_top_of_surjective,
      `HodgeConjecture.NormalizationInertia.fixedMovingBoundaryIdeal_eq_top_of_surjective,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_of_surjective,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels,
      `HodgeConjecture.NormalizationInertia.Diagram.exists_one_lt_inertiaIndex,
      `HodgeConjecture.NormalizationInertia.Diagram.ramifiedCodimensionOnePoint_isEmpty,
      `HodgeConjecture.NormalizationInertia.Diagram.noCodimensionOneRamification,
      `HodgeConjecture.NormalizationInertia.exists_nonzero_normalizationTraceDual_denominator,
      `HodgeConjecture.NormalizationInertia.boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon,
      `HodgeConjecture.NormalizationInertia.boundarySectionSubalgebra_eq_bot_of_trace_landing,
      `HodgeConjecture.NormalizationInertia.normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot,
      `HodgeConjecture.NormalizationInertia.boundarySection_tracePoleWitness,
      `HodgeConjecture.NormalizationInertia.normalizationTraceDual_colon_eq_bot_of_heightOne,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_of_traceLanding,
      `HodgeConjecture.NormalizationInertia.Diagram.forall_inertiaSaturated_of_formallyUnramified,
      `HodgeConjecture.NormalizationInertia.Diagram.globalSheetSelectorExtension_of_formallyUnramified,
      `HodgeConjecture.NormalizationInertia.Diagram.compactifiedSubgroupProjectorExtension_nonempty_of_formallyUnramified,
      `HodgeConjecture.NormalizationInertia.Diagram.compactifiedSubgroupProjectorLift_nonempty_of_formallyUnramified] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
