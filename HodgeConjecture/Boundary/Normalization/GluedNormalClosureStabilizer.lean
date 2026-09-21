import HodgeConjecture.Boundary.Normalization.GluedNormalizationDeckComparison
import HodgeConjecture.Boundary.Normalization.GluedNormalClosureAction
import HodgeConjecture.Boundary.Normalization.GluedNormalClosureFunctionField

/-!
# The full stabilizer of the original marked refinement

The existing subgroup action preserves the marked refinement. Conversely,
the actual marked function-field comparison detects exactly that subgroup.
The full deck-group reconstruction then identifies the existing marked
action with all automorphisms over the original cover. No field marking,
normalization or action is replaced.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles SchemeCorrespondence

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

/-- A field automorphism preserves the original marked refinement exactly
when it fixes the original embedded intermediate field. -/
theorem gluedNormalizationAutomorphism_comp_toCover_iff :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).galoisGroup,
      (gluedNormalizationAutomorphism X Nₚ σ).hom ≫ gluedNormalClosureToCover p hY =
          gluedNormalClosureToCover p hY ↔
        σ ∈ (functionFieldNormalClosureData p).intermediateFixingSubgroup := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  intro σ
  constructor
  · intro h
    apply (IntermediateField.mem_fixingSubgroup_iff
      (functionFieldNormalClosureData p).intermediateField σ).mpr
    intro z hz
    obtain ⟨c, rfl⟩ := hz
    have hf : functionFieldMapOfDominant (gluedNormalClosureToCover p hY) ≫
        functionFieldMapOfDominant (gluedNormalizationAutomorphism X Nₚ σ).hom =
        functionFieldMapOfDominant (gluedNormalClosureToCover p hY) := by
      rw [← functionFieldMapOfDominant_comp]
      congr 1
    have hc := congrArg (gluedNormalizationFunctionFieldEquiv X Nₚ)
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hf) c)
    change gluedNormalizationFunctionFieldEquiv X Nₚ
      (functionFieldMapOfDominant (gluedNormalizationAutomorphism X Nₚ σ).hom
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c)) =
      gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) at hc
    rw [gluedNormalizationFunctionFieldEquiv_automorphism,
      gluedNormalClosureFunctionFieldEquiv_toCover] at hc
    have hs := congrArg σ hc
    simpa only [AlgEquiv.apply_symm_apply] using hs.symm
  · intro h
    exact gluedNormalizationAutomorphism_comp_toCover p hY ⟨σ, h⟩

/-- For an arbitrary deck transformation over the base, the reconstructed
field automorphism detects preservation of the same marked refinement. -/
theorem gluedNormalClosureDeckTransformation_comp_toCover_iff :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ d : DeckTransformation (gluedNormalizationToBase X Nₚ),
      d.hom.left ≫ gluedNormalClosureToCover p hY = gluedNormalClosureToCover p hY ↔
        gluedNormalizationDeckFieldAutomorphism X Nₚ d ∈
          (functionFieldNormalClosureData p).intermediateFixingSubgroup := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro d
  have h := congrArg (fun e => e.hom.left)
    (gluedNormalizationDeckAction_fieldAutomorphism X Nₚ d)
  change (gluedNormalizationAutomorphism X Nₚ
    (gluedNormalizationDeckFieldAutomorphism X Nₚ d)).hom = d.hom.left at h
  rw [← h]
  exact gluedNormalizationAutomorphism_comp_toCover_iff p hY _

/-- The original marked subgroup action is faithful. -/
theorem gluedNormalClosureMarkedDeckAction_injective :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Function.Injective (gluedNormalClosureMarkedDeckAction p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro σ τ h
  apply Subtype.ext
  apply gluedNormalizationDeckAction_injective X Nₚ
  apply CategoryTheory.Aut.ext
  apply Over.OverMorphism.ext
  exact congrArg (fun d => d.hom.left) h

private def markedDeckToBase :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    DeckTransformation (gluedNormalClosureToCover p hY) →
      DeckTransformation (gluedNormalizationToBase X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro d
  refine Over.isoMk ((Over.forget Y).mapIso d) ?_
  change d.hom.left ≫ gluedNormalizationToBase X Nₚ = gluedNormalizationToBase X Nₚ
  have hd : d.hom.left ≫ gluedNormalClosureToCover p hY =
      gluedNormalClosureToCover p hY := Over.w d.hom
  rw [← gluedNormalClosureToCover_comp_toBase p hY, ← Category.assoc, hd]

private def markedDeckFieldElement :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    DeckTransformation (gluedNormalClosureToCover p hY) →
      (functionFieldNormalClosureData p).intermediateFixingSubgroup := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro d
  refine ⟨gluedNormalizationDeckFieldAutomorphism X Nₚ (markedDeckToBase p hY d), ?_⟩
  apply (gluedNormalClosureDeckTransformation_comp_toCover_iff p hY
    (markedDeckToBase p hY d)).mp
  change d.hom.left ≫ gluedNormalClosureToCover p hY = gluedNormalClosureToCover p hY
  exact Over.w d.hom

private theorem markedDeckAction_fieldElement :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ d : DeckTransformation (gluedNormalClosureToCover p hY),
      gluedNormalClosureMarkedDeckAction p hY (markedDeckFieldElement p hY d) = d := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro d
  apply CategoryTheory.Aut.ext
  apply Over.OverMorphism.ext
  exact congrArg (fun e => e.hom.left)
    (gluedNormalizationDeckAction_fieldAutomorphism X Nₚ (markedDeckToBase p hY d))

/-- Every automorphism over the original cover is induced by the existing
marked subgroup action. -/
theorem gluedNormalClosureMarkedDeckAction_surjective :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Function.Surjective (gluedNormalClosureMarkedDeckAction p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact fun d => ⟨markedDeckFieldElement p hY d, markedDeckAction_fieldElement p hY d⟩

/-- The original marked subgroup is the full deck group of the refinement.
The forward map is the original action; the inverse is its marked field reconstruction. -/
def gluedNormalClosureMarkedDeckEquiv :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureData p).intermediateFixingSubgroup ≃*
      DeckTransformation (gluedNormalClosureToCover p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact
    { toFun := gluedNormalClosureMarkedDeckAction p hY
      invFun := markedDeckFieldElement p hY
      left_inv := fun σ => gluedNormalClosureMarkedDeckAction_injective p hY
        (markedDeckAction_fieldElement p hY (gluedNormalClosureMarkedDeckAction p hY σ))
      right_inv := markedDeckAction_fieldElement p hY
      map_mul' := (gluedNormalClosureMarkedDeckAction p hY).map_mul }

local instance markedStabilizerOverIntegral :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsIntegral (Over.mk (gluedNormalClosureToCover p hY)).left := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact inferInstanceAs (IsIntegral (gluedNormalizationModel X Nₚ))

local instance markedStabilizerBaseSurjective :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Surjective (gluedNormalizationToBase X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  exact gluedNormalizationToBase_surjective X Nₚ

local instance markedStabilizerFieldAlgebra :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra X.functionField (gluedNormalizationModel X Nₚ).functionField := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact (functionFieldMapOfDominant (gluedNormalizationToBase X Nₚ)).hom.toAlgebra

/-- The inverse marked equivalence retains the actual inverse-deck pullback
and the same field marking as the full comparison. -/
theorem gluedNormalClosureMarkedDeckEquiv_symm_apply :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ (d : DeckTransformation (gluedNormalClosureToCover p hY)) (x : Nₚ),
      ((gluedNormalClosureMarkedDeckEquiv p hY).symm d).val x =
        gluedNormalizationFunctionFieldEquiv X Nₚ
          (functionFieldMapOfDominant d.inv.left
            ((gluedNormalizationFunctionFieldEquiv X Nₚ).symm x)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro d x
  rfl

end

end HodgeConjecture.CollisionFoundations
