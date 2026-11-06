module

public import HodgeConjecture.Boundary.Normalization.GenericFiberBaseChange
public import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
public import HodgeConjecture.Boundary.Normalization.SelectorComparison

@[expose] public section

/-!
# The original normal closure splits the actual generic fiber

Apply `Spec` to the existing normal-closure tensor equivalence and then use
the actual generic base-change square. The resulting scheme isomorphism
retains both projections and sends the original base-sheet augmentation
to the point given by the original marked field embedding.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles
open scoped TensorProduct

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

theorem markedGenericPoint_commutes :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (Spec.map (CommRingCat.ofHom (functionFieldNormalClosureData p).embedding.toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ p =
      (𝟙 (Spec (.of Nₚ))) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Nₚ)) ≫
          X.fromSpecStalk (genericPoint X)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [Category.assoc, (functionFieldMapOfDominant_isPullback p).w,
    ← Category.assoc, ← Spec.map_comp, Category.id_comp]
  congr 1

variable [FormallyUnramified p]

/-- The original normal-closure sheet algebra is the actual generic fiber
after base change to the same normal-closure field. -/
def functionFieldNormalClosureSplitFiberIso :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Spec (.of (GenericSheetAlgebra Nₚ
      (functionFieldNormalClosureData p).intermediateFixingSubgroup)) ≅
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Nₚ)) ≫
        X.fromSpecStalk (genericPoint X)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra.IsSeparable X.functionField Y.functionField :=
    functionFieldMapOfDominant_isSeparable p
  let e := (functionFieldNormalClosureData p).normalClosureTensorGenericSheetsEquiv
  exact Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫
    (functionFieldMapOfDominant_baseChange_isPullback p Nₚ).isoPullback

/-- The projection to the original upstairs scheme evaluates each element
of its function field through the existing sheet embeddings. -/
theorem functionFieldNormalClosureSplitFiberIso_hom_fst :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Pi.algHom X.functionField
          (fun _ : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup => Nₚ)
          (functionFieldNormalClosureData p).sheetEmbedding).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra.IsSeparable X.functionField Y.functionField :=
    functionFieldMapOfDominant_isSeparable p
  change (Spec.map (CommRingCat.ofHom
      (functionFieldNormalClosureData p).normalClosureTensorToGenericSheets.toRingHom) ≫
    (functionFieldMapOfDominant_baseChange_isPullback p Nₚ).isoPullback.hom) ≫
      pullback.fst _ _ = _
  rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro y
  apply funext
  intro s
  change (functionFieldNormalClosureData p).normalClosureTensorToGenericSheets
    (1 ⊗ₜ[X.functionField] y) s = (functionFieldNormalClosureData p).sheetEmbedding s y
  simp

/-- The projection to the original normal-closure base is the constant-function
map of the existing sheet algebra. -/
theorem functionFieldNormalClosureSplitFiberIso_hom_snd :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap Nₚ
        (GenericSheetAlgebra Nₚ (functionFieldNormalClosureData p).intermediateFixingSubgroup))) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra.IsSeparable X.functionField Y.functionField :=
    functionFieldMapOfDominant_isSeparable p
  change (Spec.map (CommRingCat.ofHom
      (functionFieldNormalClosureData p).normalClosureTensorToGenericSheets.toRingHom) ≫
    (functionFieldMapOfDominant_baseChange_isPullback p Nₚ).isoPullback.hom) ≫
      pullback.snd _ _ = _
  rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply funext
  intro s
  change (functionFieldNormalClosureData p).normalClosureTensorToGenericSheets
    (x ⊗ₜ[X.functionField] 1) s = x
  simp

/-- The original base-sheet point becomes the actual pullback point specified
by the original marked embedding and the identity of the normal-closure base. -/
theorem functionFieldNormalClosureSplitFiberIso_baseSheet :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Spec.map (CommRingCat.ofHom
        (functionFieldNormalClosureData p).normalClosureBaseSheetAugmentation.toRingHom) ≫
      (functionFieldNormalClosureSplitFiberIso p).hom =
      pullback.lift
        (Spec.map (CommRingCat.ofHom (functionFieldNormalClosureData p).embedding.toRingHom) ≫
          Y.fromSpecStalk (genericPoint Y))
        (𝟙 (Spec (.of Nₚ))) (markedGenericPoint_commutes p) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  apply pullback.hom_ext
  · rw [Category.assoc, functionFieldNormalClosureSplitFiberIso_hom_fst,
      pullback.lift_fst, ← Category.assoc, ← Spec.map_comp]
    congr 1
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change (functionFieldNormalClosureData p).sheetEmbedding
      (baseSheet (functionFieldNormalClosureData p).intermediateFixingSubgroup) c =
        (functionFieldNormalClosureData p).embedding c
    rw [NormalClosureData.sheetEmbedding_baseSheet]
  · rw [Category.assoc, functionFieldNormalClosureSplitFiberIso_hom_snd,
      pullback.lift_snd, ← Spec.map_comp, ← Spec.map_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl

end

end HodgeConjecture.CollisionFoundations
