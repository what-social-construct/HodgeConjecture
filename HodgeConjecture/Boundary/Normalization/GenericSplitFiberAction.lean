module

public import HodgeConjecture.Boundary.Normalization.GenericSplitFiber
public import HodgeConjecture.Boundary.Normalization.GluedNormalizationFunctionFieldAction
public import HodgeConjecture.Boundary.Normalization.GluedNormalClosureFunctionField
public import HodgeConjecture.Cycles.FunctionFieldExtensionality

@[expose] public section

/-!
# Generic sheet points and the original normalization action

Evaluation at each existing Galois sheet gives a point of the actual
normal-closure generic fiber. Its upstairs projection is the corresponding
field embedding. The original normalization action realizes the same point,
with the inverse required by its existing inverse-pullback convention.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u

private theorem sheetEmbedding_mk
    {K L N : Type u} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N] (D : NormalClosureData K L N)
    (g : D.galoisGroup) (c : L) :
    D.sheetEmbedding (g : GaloisSheets D.intermediateFixingSubgroup) c =
      g (D.embedding c) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.intermediateFixingSubgroup g
  have hfix : (h : D.galoisGroup) (D.embedding c) = D.embedding c :=
    (IntermediateField.mem_fixingSubgroup_iff D.intermediateField
      (h : D.galoisGroup)).mp h.property (D.embedding c) ⟨c, rfl⟩
  change ((g : GaloisSheets D.intermediateFixingSubgroup).out : D.galoisGroup)
    (D.embedding c) = g (D.embedding c)
  rw [hh]
  change g ((h : D.galoisGroup) (D.embedding c)) = g (D.embedding c)
  rw [hfix]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

section Evaluation

variable [FormallyUnramified p]

/-- Evaluation at any original sheet projects to its original field embedding. -/
theorem functionFieldNormalClosureSplitFiberIso_eval_fst :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ s : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (Spec.map (CommRingCat.ofHom
          (Pi.evalAlgHom Nₚ
            (fun _ : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup => Nₚ)
            s).toRingHom) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
        pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom
            ((functionFieldNormalClosureData p).sheetEmbedding s).toRingHom) ≫
            Y.fromSpecStalk (genericPoint Y) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro s
  rw [Category.assoc, functionFieldNormalClosureSplitFiberIso_hom_fst,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- Every original sheet-evaluation point lies over the identity of the same
normal-closure field. -/
theorem functionFieldNormalClosureSplitFiberIso_eval_snd :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ s : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (Spec.map (CommRingCat.ofHom
          (Pi.evalAlgHom Nₚ
            (fun _ : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup => Nₚ)
            s).toRingHom) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
        pullback.snd _ _ = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro s
  rw [Category.assoc, functionFieldNormalClosureSplitFiberIso_hom_snd,
    ← Spec.map_comp, ← Spec.map_id]
  rfl

end Evaluation

local instance orbitBaseSurjective (N : Type u) [Field N] [Algebra X.functionField N]
    [FiniteDimensional X.functionField N] : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance orbitFieldAlgebra (N : Type u) [Field N] [Algebra X.functionField N]
    [FiniteDimensional X.functionField N] :
    Algebra X.functionField (gluedNormalizationModel X N).functionField :=
  (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra

variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

/-- The original sheet represented by `g` is obtained from the original
normalization generic point by the original automorphism indexed by `g⁻¹`.
This comparison does not require formal unramifiedness. -/
theorem functionFieldNormalClosureSheetPoint_eq_normalizationOrbit :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : (functionFieldNormalClosureData p).galoisGroup,
      Spec.map (CommRingCat.ofHom
          ((functionFieldNormalClosureData p).sheetEmbedding
            (g : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup)).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) =
      (Spec.map (CommRingCat.ofHom (gluedNormalizationFunctionFieldEquiv X Nₚ).toRingHom) ≫
        (gluedNormalizationModel X Nₚ).fromSpecStalk (genericPoint (gluedNormalizationModel X Nₚ))) ≫
          (gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫ gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  intro g
  rw [Category.assoc, ← functionFieldMapOfDominant_fromSpecStalk
    ((gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫ gluedNormalClosureToCover p hY),
    ← Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change (functionFieldNormalClosureData p).sheetEmbedding
    (g : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup) c =
      gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant
          ((gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫ gluedNormalClosureToCover p hY) c)
  rw [functionFieldMapOfDominant_comp]
  change _ = gluedNormalizationFunctionFieldEquiv X Nₚ
    (functionFieldMapOfDominant (gluedNormalizationAutomorphism X Nₚ g⁻¹).hom
      (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c))
  rw [gluedNormalizationFunctionFieldEquiv_automorphism,
    gluedNormalClosureFunctionFieldEquiv_toCover, sheetEmbedding_mk]
  rfl

theorem normalizationOrbit_commutes :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : (functionFieldNormalClosureData p).galoisGroup,
      ((Spec.map (CommRingCat.ofHom (gluedNormalizationFunctionFieldEquiv X Nₚ).toRingHom) ≫
        (gluedNormalizationModel X Nₚ).fromSpecStalk (genericPoint (gluedNormalizationModel X Nₚ))) ≫
          (gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫ gluedNormalClosureToCover p hY) ≫ p =
        (𝟙 (Spec (.of Nₚ))) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Nₚ)) ≫
            X.fromSpecStalk (genericPoint X)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g
  rw [← functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY g,
    Category.assoc, (functionFieldMapOfDominant_isPullback p).w,
    ← Category.assoc, ← Spec.map_comp, Category.id_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact ((functionFieldNormalClosureData p).sheetEmbedding
    (g : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup)).commutes c

/-- Under the existing split-fiber comparison, each sheet-evaluation point
is the full pullback point determined by the same normalization orbit and
the identity on the original normal-closure base. -/
theorem functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit
    [FormallyUnramified p] :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : (functionFieldNormalClosureData p).galoisGroup,
      Spec.map (CommRingCat.ofHom
          (Pi.evalAlgHom Nₚ
            (fun _ : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup => Nₚ)
            (g : GaloisSheets (functionFieldNormalClosureData p).intermediateFixingSubgroup)).toRingHom) ≫
        (functionFieldNormalClosureSplitFiberIso p).hom =
          pullback.lift
            ((Spec.map (CommRingCat.ofHom (gluedNormalizationFunctionFieldEquiv X Nₚ).toRingHom) ≫
              (gluedNormalizationModel X Nₚ).fromSpecStalk (genericPoint (gluedNormalizationModel X Nₚ))) ≫
                (gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫ gluedNormalClosureToCover p hY)
            (𝟙 (Spec (.of Nₚ))) (normalizationOrbit_commutes p hY g) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g
  apply pullback.hom_ext
  · rw [functionFieldNormalClosureSplitFiberIso_eval_fst, pullback.lift_fst,
      functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY g]
  · rw [functionFieldNormalClosureSplitFiberIso_eval_snd, pullback.lift_snd]

end

end HodgeConjecture.CollisionFoundations
