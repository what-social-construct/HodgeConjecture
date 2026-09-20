import HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedNormalClosure
import Lean.Util.CollectAxioms

/-!
SP86 regressions for target-local properties of the original glued normalization.
Run with `lake env lean research/GluedNormalizationPropertiesVerification.lean`.

The nonempty affine chart cover is checked for arbitrary schemes, including the
empty scheme. The target-local equivalence retains the actual generic-germ
scalar map and original chart structural maps. Global affineness is tested
without finite-degree, normality, Noetherianity, or separatedness assumptions,
including inverse images of arbitrary affine opens and the empty open. The
finite and étale equivalences are exercised in both directions. Finally, the
actual marked function-field normal closure is specialized with explicit normal
stalk hypotheses and no Noetherian or perfect-field assumption. The exact audit
registry checks all six new public declarations, including the affine instance.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations
open HodgeConjecture.SchemeCycles HodgeConjecture.NormalizationInertia

noncomputable section

universe u

section ActualBaseCover

example (X : Scheme.{u}) :
    (⨆ U : NonemptyAffineChart X, U.val) = ⊤ :=
  nonemptyAffineChart_iSup_eq_top X

example :
    (⨆ U : NonemptyAffineChart Scheme.empty.{u}, U.val) = ⊤ :=
  nonemptyAffineChart_iSup_eq_top Scheme.empty

example (X : Scheme.{u}) [IsEmpty X] : IsEmpty (NonemptyAffineChart X) := by
  refine ⟨fun U => ?_⟩
  obtain ⟨x⟩ := U.property.2
  exact isEmptyElim x.val

example (X : Scheme.{u}) (x : X) :
    ∃ U : NonemptyAffineChart X, x ∈ U.val := by
  have hx : x ∈ (⨆ U : NonemptyAffineChart X, U.val) := by
    rw [nonemptyAffineChart_iSup_eq_top]
    trivial
  simpa only [TopologicalSpace.Opens.mem_iSup] using hx

end ActualBaseCover

section OriginalStructuralMaps

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance verificationAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example (U : NonemptyAffineChart X) :
    (normalizationChartPreimageIso X N U).hom ≫
      (gluedNormalizationToBase X N ∣_ U.val) =
      normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv :=
  normalizationChartPreimageIso_hom_comp_restrict X N U

example (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (U : NonemptyAffineChart X) :
    P (gluedNormalizationToBase X N ∣_ U.val) ↔
      P (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) := by
  have h := P.cancel_left_of_respectsIso (normalizationChartPreimageIso X N U).hom
    (gluedNormalizationToBase X N ∣_ U.val)
  rw [normalizationChartPreimageIso_hom_comp_restrict] at h
  exact h.symm

example (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P (gluedNormalizationToBase X N) ↔
      ∀ U : NonemptyAffineChart X,
        P (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  gluedNormalizationToBase_property_iff X N P

example (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : P (gluedNormalizationToBase X N)) (U : NonemptyAffineChart X) :
    P (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  (gluedNormalizationToBase_property_iff X N P).mp h U

example (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : NonemptyAffineChart X,
      P (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv)) :
    P (gluedNormalizationToBase X N) :=
  (gluedNormalizationToBase_property_iff X N P).mpr h

example : IsAffineHom (gluedNormalizationToBase X N) := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : Scheme.IsSeparated X := inferInstance
  exact gluedNormalizationToBase_isAffineHom X N

example (U : NonemptyAffineChart X) :
    IsAffineHom (gluedNormalizationToBase X N) ∧
      IsAffineOpen ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  exact ⟨inferInstance, U.property.1.preimage (gluedNormalizationToBase X N)⟩

example (V : X.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen ((gluedNormalizationToBase X N) ⁻¹ᵁ V) :=
  hV.preimage (gluedNormalizationToBase X N)

example (V : X.Opens) (hV : IsAffineOpen V) :
    IsAffine (((gluedNormalizationToBase X N) ⁻¹ᵁ V).toScheme) :=
  hV.preimage (gluedNormalizationToBase X N)

example : IsAffineOpen ((gluedNormalizationToBase X N) ⁻¹ᵁ (⊥ : X.Opens)) :=
  (isAffineOpen_bot X).preimage (gluedNormalizationToBase X N)

example (V : X.Opens) : IsAffineHom (gluedNormalizationToBase X N ∣_ V) :=
  IsZariskiLocalAtTarget.restrict
    (P := @IsAffineHom) (gluedNormalizationToBase_isAffineHom X N) V

example :
    IsFinite (gluedNormalizationToBase X N) ↔
      ∀ U : NonemptyAffineChart X,
        IsFinite (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  gluedNormalizationToBase_isFinite_iff X N

example (h : IsFinite (gluedNormalizationToBase X N)) (U : NonemptyAffineChart X) :
    IsFinite (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  (gluedNormalizationToBase_isFinite_iff X N).mp h U

example (h : ∀ U : NonemptyAffineChart X,
    IsFinite (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv)) :
    IsFinite (gluedNormalizationToBase X N) :=
  (gluedNormalizationToBase_isFinite_iff X N).mpr h

example (h : IsFinite (gluedNormalizationToBase X N)) (V : X.Opens) :
    IsFinite (gluedNormalizationToBase X N ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @IsFinite) h V

example :
    IsEtale (gluedNormalizationToBase X N) ↔
      ∀ U : NonemptyAffineChart X,
        IsEtale (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  gluedNormalizationToBase_isEtale_iff X N

example (h : IsEtale (gluedNormalizationToBase X N)) (U : NonemptyAffineChart X) :
    IsEtale (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  (gluedNormalizationToBase_isEtale_iff X N).mp h U

example (h : ∀ U : NonemptyAffineChart X,
    IsEtale (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv)) :
    IsEtale (gluedNormalizationToBase X N) :=
  (gluedNormalizationToBase_isEtale_iff X N).mpr h

example (h : IsEtale (gluedNormalizationToBase X N)) (V : X.Opens) :
    IsEtale (gluedNormalizationToBase X N ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @IsEtale) h V

end OriginalStructuralMaps

section ActualNormalClosure

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [IsEtale p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap X.functionField Y.functionField = (functionFieldMapOfDominant p).hom := rfl

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U.val) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
    algebraMap Γ(X, U.val) Nₚ b =
      algebraMap X.functionField Nₚ ((X.germToFunctionField U.val).hom b) := rfl

variable (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsFinite (gluedNormalizationToBase X Nₚ) ∧
      IsEtale (gluedNormalizationToBase X Nₚ) := by
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact functionFieldNormalClosure_glued_finite_etale p hX hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsFinite (gluedNormalizationToBase X Nₚ) :=
  (functionFieldNormalClosure_glued_finite_etale p hX hY).1

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsEtale (gluedNormalizationToBase X Nₚ) :=
  (functionFieldNormalClosure_glued_finite_etale p hX hY).2

example (V : X.Opens) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsFinite (gluedNormalizationToBase X Nₚ ∣_ V) ∧
      IsEtale (gluedNormalizationToBase X Nₚ ∣_ V) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  have h := functionFieldNormalClosure_glued_finite_etale p hX hY
  exact ⟨IsZariskiLocalAtTarget.restrict (P := @IsFinite) h.1 V,
    IsZariskiLocalAtTarget.restrict (P := @IsEtale) h.2 V⟩

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U.val) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
    IsFinite (normalizedModelToBase Γ(X, U.val) Nₚ ≫ U.property.1.isoSpec.inv) ∧
      IsEtale (normalizedModelToBase Γ(X, U.val) Nₚ ≫ U.property.1.isoSpec.inv) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U.val) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
  have h := functionFieldNormalClosure_glued_finite_etale p hX hY
  exact ⟨(gluedNormalizationToBase_isFinite_iff X Nₚ).mp h.1 U,
    (gluedNormalizationToBase_isEtale_iff X Nₚ).mp h.2 U⟩

end ActualNormalClosure

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.nonemptyAffineChart_iSup_eq_top,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationToBase_property_iff,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationToBase_isAffineHom,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationToBase_isFinite_iff,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationToBase_isEtale_iff,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosure_glued_finite_etale]
  unless declarations.length == 6 do
    throwError "Expected exactly 6 SP86 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP86 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP86 audit registry: 6 distinct public declarations"
