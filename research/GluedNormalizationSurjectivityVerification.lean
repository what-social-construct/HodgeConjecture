import HodgeConjecture.Boundary.Normalization.GluedNormalizationSurjectivity
import HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedRefinement
import Lean.Util.CollectAxioms

/-!
SP89 regressions for surjectivity of the original global normalization maps.
Run with `lake env lean research/GluedNormalizationSurjectivityVerification.lean`.

The structural map is tested for an arbitrary function-field extension, with
no finite-dimensionality, algebraicity, normal-base, or Noetherian input. Its
point lifts and restrictions retain the original charts and germ scalars. The
marked refinement is tested separately for finite dominant maps with explicit
normal stalks upstairs, without étaleness or normality downstairs. Its original
chart formula supplies direct lifts through the marked affine refinement.
Integrated finite étale surjectivity uses the stronger hypotheses explicitly.
The exact audit registry checks the two new public surjectivity declarations.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open HodgeConjecture.NormalizationInertia

noncomputable section

universe u

section ArbitraryFieldExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance surjectivityVerificationAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example : Surjective (gluedNormalizationToBase X N) := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsAlgebraic X.functionField N := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  exact gluedNormalizationToBase_surjective X N

example : Function.Surjective (gluedNormalizationToBase X N).base :=
  (gluedNormalizationToBase_surjective X N).surj

example (x : X) : ∃ z : gluedNormalizationModel X N,
    (gluedNormalizationToBase X N).base z = x :=
  (gluedNormalizationToBase_surjective X N).surj x

example : Set.range (gluedNormalizationToBase X N).base = Set.univ :=
  Set.range_eq_univ.mpr (gluedNormalizationToBase_surjective X N).surj

example (V : X.Opens) : Surjective (gluedNormalizationToBase X N ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @Surjective)
    (gluedNormalizationToBase_surjective X N) V

example (V : X.Opens) (x : V.toScheme) :
    ∃ z : ((gluedNormalizationToBase X N) ⁻¹ᵁ V).toScheme,
      (gluedNormalizationToBase X N ∣_ V).base z = x :=
  (IsZariskiLocalAtTarget.restrict (P := @Surjective)
    (gluedNormalizationToBase_surjective X N) V).surj x

example : Surjective (gluedNormalizationToBase X N ∣_ (⊥ : X.Opens)) :=
  IsZariskiLocalAtTarget.restrict (P := @Surjective)
    (gluedNormalizationToBase_surjective X N) ⊥

example (U : NonemptyAffineChart X) :
    Surjective (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  exact (gluedNormalizationToBase_property_iff X N (@Surjective)).mp
    (gluedNormalizationToBase_surjective X N) U

example (U : NonemptyAffineChart X) (x : X) (hx : x ∈ U.val) :
    ∃ a : (affineNormalizationDiagram X N).obj U,
      (gluedNormalizationToBase X N).base ((normalizationChartToGlued X N U).base a) = x := by
  obtain ⟨z, hz⟩ := (gluedNormalizationToBase_surjective X N).surj x
  have hzU : z ∈ Set.range (normalizationChartToGlued X N U).base := by
    rw [normalizationChartToGlued_range]
    change (gluedNormalizationToBase X N).base z ∈ U.val
    rw [hz]
    exact hx
  obtain ⟨a, ha⟩ := hzU
  exact ⟨a, by rw [ha]; exact hz⟩

end ArbitraryFieldExtension

section ActualMarkedRefinement

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap X.functionField Y.functionField = (functionFieldMapOfDominant p).hom := rfl

example (a : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding a : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) a :=
  functionFieldNormalClosureData_embedding_apply p a

example : Surjective (gluedNormalClosureToCover p hY) := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact gluedNormalClosureToCover_surjective p hY

example : Function.Surjective (gluedNormalClosureToCover p hY).base :=
  (gluedNormalClosureToCover_surjective p hY).surj

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ y : Y, ∃ z : gluedNormalizationModel X Nₚ,
      (gluedNormalClosureToCover p hY).base z = y :=
  (gluedNormalClosureToCover_surjective p hY).surj

example (V : Y.Opens) : Surjective (gluedNormalClosureToCover p hY ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @Surjective)
    (gluedNormalClosureToCover_surjective p hY) V

example (V : Y.Opens) (y : V.toScheme) :
    ∃ z : ((gluedNormalClosureToCover p hY) ⁻¹ᵁ V).toScheme,
      (gluedNormalClosureToCover p hY ∣_ V).base z = y :=
  (IsZariskiLocalAtTarget.restrict (P := @Surjective)
    (gluedNormalClosureToCover_surjective p hY) V).surj y

example : Surjective (gluedNormalClosureToCover p hY ∣_ (⊥ : Y.Opens)) :=
  IsZariskiLocalAtTarget.restrict (P := @Surjective)
    (gluedNormalClosureToCover_surjective p hY) ⊥

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  exact normalizationChartToGlued_comp_toCover p hY U

example (U : NonemptyAffineChart X) (y : Y) (hy : p.base y ∈ U.val) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∃ a : (affineNormalizationDiagram X Nₚ).obj U,
      (gluedNormalClosureToCover p hY).base ((normalizationChartToGlued X Nₚ U).base a) = y := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  let q := finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
    (fun y => hY y.val)
  have hq : Surjective q := finiteEtaleAffineNormalClosureToPreimage_surjective
    p U.val U.property.1 (fun y => hY y.val)
  obtain ⟨a, ha⟩ := hq.surj ⟨y, hy⟩
  refine ⟨a, ?_⟩
  rw [← Scheme.comp_base_apply, normalizationChartToGlued_comp_toCover]
  change (p ⁻¹ᵁ U.val).ι.base (q.base a) = y
  rw [ha]
  rfl

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Surjective (gluedNormalClosureToCover p hY) ∧
      gluedNormalClosureToCover p hY ≫ p = gluedNormalizationToBase X Nₚ :=
  ⟨gluedNormalClosureToCover_surjective p hY,
    gluedNormalClosureToCover_comp_toBase p hY⟩

section FiniteEtale

variable [IsEtale p]
variable (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

example : IsFinite (gluedNormalClosureToCover p hY) ∧
    IsEtale (gluedNormalClosureToCover p hY) ∧
    Surjective (gluedNormalClosureToCover p hY) := by
  have h := gluedNormalClosureToCover_finite_etale p hX hY
  exact ⟨h.1, h.2, gluedNormalClosureToCover_surjective p hY⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsFinite (gluedNormalizationToBase X Nₚ) ∧
      IsEtale (gluedNormalizationToBase X Nₚ) ∧
      Surjective (gluedNormalizationToBase X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  have h := functionFieldNormalClosure_glued_finite_etale p hX hY
  exact ⟨h.1, h.2, gluedNormalizationToBase_surjective X Nₚ⟩

example (V : Y.Opens) : IsFinite (gluedNormalClosureToCover p hY ∣_ V) ∧
    IsEtale (gluedNormalClosureToCover p hY ∣_ V) ∧
    Surjective (gluedNormalClosureToCover p hY ∣_ V) := by
  have h := gluedNormalClosureToCover_finite_etale p hX hY
  exact ⟨IsZariskiLocalAtTarget.restrict (P := @IsFinite) h.1 V,
    IsZariskiLocalAtTarget.restrict (P := @IsEtale) h.2 V,
    IsZariskiLocalAtTarget.restrict (P := @Surjective)
      (gluedNormalClosureToCover_surjective p hY) V⟩

end FiniteEtale

end ActualMarkedRefinement

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.gluedNormalizationToBase_surjective,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureToCover_surjective]
  unless declarations.length == 2 do
    throwError "Expected exactly 2 SP89 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP89 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP89 audit registry: 2 distinct public declarations"
