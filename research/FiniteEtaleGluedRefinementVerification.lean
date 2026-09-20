import HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedRefinement
import Lean.Util.CollectAxioms

/-!
SP88 regressions for finite étaleness of the original glued marked refinement.
Run with `lake env lean research/FiniteEtaleGluedRefinementVerification.lean`.

Generic finite cancellation is tested with only a finite composite and a
separated second leg, without finiteness of that leg or integral schemes.
Its restrictions, affine consequence, and iterated use are also exercised.
The actual refinement tests retain the original generic field marking,
germ-derived scalar action, chart maps, and base triangle. The finite étale
conclusion and its arbitrary-open restrictions use the explicit normal-stalk
hypotheses without Noetherian or perfect-field inputs. The exact audit registry
checks both new public declarations against the three standard Lean axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open HodgeConjecture.NormalizationInertia

noncomputable section

universe u

section GenericCancellation

variable {Z Y X W : Scheme.{u}}

example (f : Z ⟶ Y) (g : Y ⟶ X) [IsFinite (f ≫ g)] [IsSeparated g] :
    IsFinite f := by
  fail_if_success have _ : IsFinite g := inferInstance
  fail_if_success have _ : IsEtale g := inferInstance
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsIntegral Y := inferInstance
  fail_if_success have _ : IsIntegral Z := inferInstance
  exact isFinite_of_comp_of_isSeparated f g

example (f : Z ⟶ Y) (g : Y ⟶ X) [IsFinite (f ≫ g)] [IsSeparated g]
    (V : Y.Opens) : IsFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @IsFinite)
    (isFinite_of_comp_of_isSeparated f g) V

example (f : Z ⟶ Y) (g : Y ⟶ X) [IsFinite (f ≫ g)] [IsSeparated g] :
    IsAffineHom f := by
  letI : IsFinite f := isFinite_of_comp_of_isSeparated f g
  infer_instance

example (f : Z ⟶ Y) (g : Y ⟶ X) (h : X ⟶ W)
    [IsFinite ((f ≫ g) ≫ h)] [IsSeparated g] [IsSeparated h] :
    IsFinite f := by
  letI : IsFinite (f ≫ g) := isFinite_of_comp_of_isSeparated (f ≫ g) h
  exact isFinite_of_comp_of_isSeparated f g

example (f : Z ⟶ Y) (g : Y ⟶ X) [IsFinite (f ≫ g)] [IsOpenImmersion g] :
    IsFinite f := by
  fail_if_success have _ : IsFinite g := inferInstance
  exact isFinite_of_comp_of_isSeparated f g

example (f : Z ⟶ Y) (g : Y ⟶ X) [IsFinite (f ≫ g)] [Mono g] :
    IsFinite f :=
  isFinite_of_comp_of_isSeparated f g

end GenericCancellation

section ActualRefinement

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [IsEtale p]
variable (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

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

example : IsFinite (gluedNormalClosureToCover p hY) ∧
    IsEtale (gluedNormalClosureToCover p hY) := by
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact gluedNormalClosureToCover_finite_etale p hX hY

example : IsFinite (gluedNormalClosureToCover p hY) :=
  (gluedNormalClosureToCover_finite_etale p hX hY).1

example : IsEtale (gluedNormalClosureToCover p hY) :=
  (gluedNormalClosureToCover_finite_etale p hX hY).2

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureToCover p hY ≫ p = gluedNormalizationToBase X Nₚ :=
  gluedNormalClosureToCover_comp_toBase p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsFinite (gluedNormalClosureToCover p hY) ∧
      IsEtale (gluedNormalClosureToCover p hY) ∧
      gluedNormalClosureToCover p hY ≫ p = gluedNormalizationToBase X Nₚ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  have h := gluedNormalClosureToCover_finite_etale p hX hY
  exact ⟨h.1, h.2, gluedNormalClosureToCover_comp_toBase p hY⟩

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι :=
  normalizationChartToGlued_comp_toCover p hY U

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ a : (affineNormalizationDiagram X Nₚ).obj U,
      (gluedNormalClosureToCover p hY).base ((normalizationChartToGlued X Nₚ U).base a) =
        (p ⁻¹ᵁ U.val).ι.base
          ((finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val)).base a) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro a
  rw [← Scheme.comp_base_apply, normalizationChartToGlued_comp_toCover]
  rfl

example (U : NonemptyAffineChart X) :
    IsFinite (finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
      (fun y => hY y.val)) ∧
      IsEtale (finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val)) :=
  finiteEtaleAffineNormalClosureToPreimage_finite_etale p U.val U.property.1
    (fun x => hX x.val) (fun y => hY y.val)

example (V : Y.Opens) : IsFinite (gluedNormalClosureToCover p hY ∣_ V) ∧
    IsEtale (gluedNormalClosureToCover p hY ∣_ V) := by
  have h := gluedNormalClosureToCover_finite_etale p hX hY
  exact ⟨IsZariskiLocalAtTarget.restrict (P := @IsFinite) h.1 V,
    IsZariskiLocalAtTarget.restrict (P := @IsEtale) h.2 V⟩

example (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen ((gluedNormalClosureToCover p hY) ⁻¹ᵁ V) := by
  letI : IsFinite (gluedNormalClosureToCover p hY) :=
    (gluedNormalClosureToCover_finite_etale p hX hY).1
  exact hV.preimage (gluedNormalClosureToCover p hY)

example : IsFinite (gluedNormalClosureToCover p hY ∣_ (⊥ : Y.Opens)) ∧
    IsEtale (gluedNormalClosureToCover p hY ∣_ (⊥ : Y.Opens)) := by
  have h := gluedNormalClosureToCover_finite_etale p hX hY
  exact ⟨IsZariskiLocalAtTarget.restrict (P := @IsFinite) h.1 ⊥,
    IsZariskiLocalAtTarget.restrict (P := @IsEtale) h.2 ⊥⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsFinite (gluedNormalizationToBase X Nₚ) ∧
      IsEtale (gluedNormalizationToBase X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsFinite (gluedNormalClosureToCover p hY) :=
    (gluedNormalClosureToCover_finite_etale p hX hY).1
  letI : IsEtale (gluedNormalClosureToCover p hY) :=
    (gluedNormalClosureToCover_finite_etale p hX hY).2
  rw [← gluedNormalClosureToCover_comp_toBase p hY]
  constructor <;> infer_instance

end ActualRefinement

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.isFinite_of_comp_of_isSeparated,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureToCover_finite_etale]
  unless declarations.length == 2 do
    throwError "Expected exactly 2 SP88 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP88 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP88 audit registry: 2 distinct public declarations"
