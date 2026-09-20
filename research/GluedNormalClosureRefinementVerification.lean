import HodgeConjecture.Boundary.Normalization.GluedNormalClosureRefinement
import HodgeConjecture.Boundary.Normalization.GluedNormalizationChart
import Lean.Util.CollectAxioms

/-!
SP87 regressions for descent of the original marked normal-closure refinement.
Run with `lake env lean research/GluedNormalClosureRefinementVerification.lean`.

All normal-closure fields use the original dominant function-field map. The
cocone uses the existing marked affine refinement to the actual inverse-image
open in the original cover. Tests check those maps, their naturality, the
descended chart formula and base triangle, uniqueness from the original marked
chart formulas, actual inverse-image compatibility, and independence of normal
stalk proofs. Only integral schemes, a finite dominant map, and explicit normal
stalks upstairs are supplied; étaleness, normality downstairs, Noetherianity,
and perfectness are not supplied. All five new public declarations, including
the cocone and descended map definitions, have an exact axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open HodgeConjecture.NormalizationInertia

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

section OriginalMarking

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

example (a : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding a : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) a :=
  functionFieldNormalClosureData_embedding_apply p a

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U.val) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
    (affineNormalizationDiagram X Nₚ).obj U =
      normalClosureNormalization (B := Γ(X, U.val)) (N := Nₚ) := rfl

end OriginalMarking

variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

section OriginalCocone

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (affineNormalClosureRefinementCocone p hY).pt = Y := rfl

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (affineNormalClosureRefinementCocone p hY).ι.app U =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := rfl

example {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (affineNormalizationDiagram X Nₚ).map f ≫
      (affineNormalClosureRefinementCocone p hY).ι.app V =
      (affineNormalClosureRefinementCocone p hY).ι.app U := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  simpa only [Functor.const_obj_map, Category.comp_id] using
    (affineNormalClosureRefinementCocone p hY).ι.naturality f

example {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (affineNormalizationDiagram X Nₚ).map f ≫
        (finiteEtaleAffineNormalClosureToPreimage p V.val V.property.1
          (fun y => hY y.val) ≫ (p ⁻¹ᵁ V.val).ι) =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  simpa only [Functor.const_obj_map, Category.comp_id] using
    (affineNormalClosureRefinementCocone p hY).ι.naturality f

end OriginalCocone

section DescendedMap

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureToCover p hY =
      colimit.desc (affineNormalizationDiagram X Nₚ)
        (affineNormalClosureRefinementCocone p hY) := rfl

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact normalizationChartToGlued_comp_toCover p hY U

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY =
      (affineNormalClosureRefinementCocone p hY).ι.app U :=
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

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureToCover p hY ≫ p = gluedNormalizationToBase X Nₚ := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  exact gluedNormalClosureToCover_comp_toBase p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ z : gluedNormalizationModel X Nₚ,
      p.base ((gluedNormalClosureToCover p hY).base z) =
        (gluedNormalizationToBase X Nₚ).base z := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro z
  rw [← Scheme.comp_base_apply, gluedNormalClosureToCover_comp_toBase]

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY ≫ p =
      (affineNormalizationBaseCocone X Nₚ).ι.app U := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [gluedNormalClosureToCover_comp_toBase, normalizationChartToGlued_comp_toBase]

example {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (affineNormalizationDiagram X Nₚ).map f ≫
        normalizationChartToGlued X Nₚ V ≫ gluedNormalClosureToCover p hY =
      normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← Category.assoc, normalizationChartToGlued_naturality]

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (normalizationChartPreimageIso X Nₚ U).hom ≫
        ((gluedNormalizationToBase X Nₚ) ⁻¹ᵁ U.val).ι ≫
        gluedNormalClosureToCover p hY =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← Category.assoc, normalizationChartPreimageIso_hom_comp_inclusion,
    normalizationChartToGlued_comp_toCover]

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (normalizationChartPreimageIso X Nₚ U).inv ≫
        (finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
          (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι) =
      ((gluedNormalizationToBase X Nₚ) ⁻¹ᵁ U.val).ι ≫
        gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← normalizationChartToGlued_comp_toCover p hY U, ← Category.assoc,
    normalizationChartPreimageIso_inv_comp_chart]

end DescendedMap

section MarkedUniqueness

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ g : gluedNormalizationModel X Nₚ ⟶ Y,
      (∀ U : NonemptyAffineChart X,
        normalizationChartToGlued X Nₚ U ≫ g =
          finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι) →
      g = gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro g hg
  exact gluedNormalClosureToCover_unique p hY g hg

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∃! g : gluedNormalizationModel X Nₚ ⟶ Y,
      ∀ U : NonemptyAffineChart X,
        normalizationChartToGlued X Nₚ U ≫ g =
          finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact ⟨gluedNormalClosureToCover p hY,
    normalizationChartToGlued_comp_toCover p hY,
    fun g hg => gluedNormalClosureToCover_unique p hY g hg⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ g k : gluedNormalizationModel X Nₚ ⟶ Y,
      (∀ U : NonemptyAffineChart X,
        normalizationChartToGlued X Nₚ U ≫ g =
          finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι) →
      (∀ U : NonemptyAffineChart X,
        normalizationChartToGlued X Nₚ U ≫ k =
          finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι) →
      g = k := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro g k hg hk
  exact (gluedNormalClosureToCover_unique p hY g hg).trans
    (gluedNormalClosureToCover_unique p hY k hk).symm

variable (hY' : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    affineNormalClosureRefinementCocone p hY =
      affineNormalClosureRefinementCocone p hY' := rfl

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureToCover p hY = gluedNormalClosureToCover p hY' := rfl

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY' y.val) ≫ (p ⁻¹ᵁ U.val).ι :=
  normalizationChartToGlued_comp_toCover p hY' U

end MarkedUniqueness

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.affineNormalClosureRefinementCocone,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureToCover,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_comp_toCover,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureToCover_comp_toBase,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureToCover_unique]
  unless declarations.length == 5 do
    throwError "Expected exactly 5 SP87 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP87 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP87 audit registry: 5 distinct public declarations"
