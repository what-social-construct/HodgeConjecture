module

import HodgeConjecture.Boundary.Normalization.GluedNormalizationChart
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP85 regressions for the original normalization charts as actual global inverse images.
Run with `lake env lean research/GluedNormalizationChartVerification.lean`.

The tests retain the original generic-germ scalar map into the fixed ambient field.
They check exact ranges, pointwise existence and uniqueness of chart lifts, the
actual inverse-image scheme isomorphisms, their original structural maps, and
compatibility with nested chart restrictions. Affineness is inherited from the
original charts. Only integrality of the original scheme and its fixed ambient
field extension are supplied. The exact audit registry checks all seven new
public declarations against the three standard Lean axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations

noncomputable section

universe u

section OriginalObjects

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable (U : NonemptyAffineChart X)

example (b : Γ(X, U.val)) :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    (affineNormalizationDiagram X N).obj U = normalizedAffineModel Γ(X, U.val) N := rfl

example :
    Set.range (normalizationChartToGlued X N U).base =
      (gluedNormalizationToBase X N).base ⁻¹' (U.val : Set X) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  exact normalizationChartToGlued_range X N U

example (z : gluedNormalizationModel X N) :
    z ∈ Set.range (normalizationChartToGlued X N U).base ↔
      (gluedNormalizationToBase X N).base z ∈ U.val := by
  rw [normalizationChartToGlued_range]
  rfl

example (z : gluedNormalizationModel X N) :
    (∃ a : (affineNormalizationDiagram X N).obj U,
      (normalizationChartToGlued X N U).base a = z) ↔
      (gluedNormalizationToBase X N).base z ∈ U.val := by
  change z ∈ Set.range (normalizationChartToGlued X N U).base ↔ _
  rw [normalizationChartToGlued_range]
  rfl

example (z : gluedNormalizationModel X N)
    (hz : (gluedNormalizationToBase X N).base z ∈ U.val) :
    ∃ a : (affineNormalizationDiagram X N).obj U,
      (normalizationChartToGlued X N U).base a = z := by
  have hmem : z ∈ Set.range (normalizationChartToGlued X N U).base := by
    rw [normalizationChartToGlued_range]
    exact hz
  exact hmem

example (z : gluedNormalizationModel X N)
    (hz : (gluedNormalizationToBase X N).base z ∈ U.val) :
    ∃! a : (affineNormalizationDiagram X N).obj U,
      (normalizationChartToGlued X N U).base a = z := by
  have hmem : z ∈ Set.range (normalizationChartToGlued X N U).base := by
    rw [normalizationChartToGlued_range]
    exact hz
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact (normalizationChartToGlued X N U).isOpenEmbedding.injective (hb.trans ha.symm)

example :
    (normalizationChartToGlued X N U).opensRange =
      (gluedNormalizationToBase X N) ⁻¹ᵁ U.val :=
  normalizationChartToGlued_opensRange X N U

example : IsAffine ((affineNormalizationDiagram X N).obj U) := by
  change IsAffine (Spec _)
  infer_instance

example : IsAffineOpen ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val) := by
  haveI : IsAffine ((affineNormalizationDiagram X N).obj U) := by
    change IsAffine (Spec _)
    infer_instance
  rw [← normalizationChartToGlued_opensRange]
  exact isAffineOpen_opensRange (normalizationChartToGlued X N U)

example : IsAffine (((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).toScheme) := by
  haveI : IsAffine ((affineNormalizationDiagram X N).obj U) := by
    change IsAffine (Spec _)
    infer_instance
  exact IsAffine.of_isIso (normalizationChartPreimageIso X N U).inv

end OriginalObjects

section ActualInverseImages

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable (U : NonemptyAffineChart X)

example :
    normalizationChartPreimageIso X N U =
      (normalizationChartToGlued X N U).isoOpensRange ≪≫
        (gluedNormalizationModel X N).isoOfEq
          (normalizationChartToGlued_opensRange X N U) := rfl

example :
    (normalizationChartPreimageIso X N U).hom ≫
      (normalizationChartPreimageIso X N U).inv = 𝟙 _ :=
  (normalizationChartPreimageIso X N U).hom_inv_id

example :
    (normalizationChartPreimageIso X N U).inv ≫
      (normalizationChartPreimageIso X N U).hom = 𝟙 _ :=
  (normalizationChartPreimageIso X N U).inv_hom_id

example :
    (normalizationChartPreimageIso X N U).hom ≫
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι =
      normalizationChartToGlued X N U :=
  normalizationChartPreimageIso_hom_comp_inclusion X N U

example :
    (normalizationChartPreimageIso X N U).inv ≫ normalizationChartToGlued X N U =
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι :=
  normalizationChartPreimageIso_inv_comp_chart X N U

example (a : (affineNormalizationDiagram X N).obj U) :
    (((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι).base
        ((normalizationChartPreimageIso X N U).hom.base a) =
      (normalizationChartToGlued X N U).base a := by
  rw [← Scheme.Hom.comp_apply, normalizationChartPreimageIso_hom_comp_inclusion]

example (z : ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).toScheme) :
    (normalizationChartToGlued X N U).base
        ((normalizationChartPreimageIso X N U).inv.base z) =
      (((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι).base z := by
  rw [← Scheme.Hom.comp_apply, normalizationChartPreimageIso_inv_comp_chart]

example (a : (affineNormalizationDiagram X N).obj U) :
    (gluedNormalizationToBase X N).base ((normalizationChartToGlued X N U).base a) ∈
      U.val := by
  have hmem : (normalizationChartToGlued X N U).base a ∈
      Set.range (normalizationChartToGlued X N U).base := ⟨a, rfl⟩
  rw [normalizationChartToGlued_range] at hmem
  exact hmem

example :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    (normalizationChartPreimageIso X N U).hom ≫
      (gluedNormalizationToBase X N ∣_ U.val) =
      normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv :=
  normalizationChartPreimageIso_hom_comp_restrict X N U

example (a : (affineNormalizationDiagram X N).obj U) :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    (gluedNormalizationToBase X N ∣_ U.val).base
        ((normalizationChartPreimageIso X N U).hom.base a) =
      (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv).base a := by
  dsimp only
  rw [← Scheme.Hom.comp_apply, normalizationChartPreimageIso_hom_comp_restrict]
  rfl

example :
    (normalizationChartPreimageIso X N U).hom ≫
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι ≫
      gluedNormalizationToBase X N =
      (affineNormalizationBaseCocone X N).ι.app U := by
  rw [← Category.assoc, normalizationChartPreimageIso_hom_comp_inclusion,
    normalizationChartToGlued_comp_toBase]

example :
    (normalizationChartPreimageIso X N U).inv ≫
      (affineNormalizationBaseCocone X N).ι.app U =
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι ≫
        gluedNormalizationToBase X N := by
  rw [← normalizationChartToGlued_comp_toBase, ← Category.assoc,
    normalizationChartPreimageIso_inv_comp_chart]

end ActualInverseImages

section RestrictionCompatibility

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable {U V W : NonemptyAffineChart X}

example (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫
      (normalizationChartPreimageIso X N V).hom =
      (normalizationChartPreimageIso X N U).hom ≫
        (gluedNormalizationModel X N).homOfLE
          (show (gluedNormalizationToBase X N) ⁻¹ᵁ U.val ≤
              (gluedNormalizationToBase X N) ⁻¹ᵁ V.val from by
            intro z hz
            exact (show U.val ≤ V.val from leOfHom f) hz) :=
  normalizationChartPreimageIso_naturality X N f

example (f : U ⟶ V) (a : (affineNormalizationDiagram X N).obj U) :
    (normalizationChartPreimageIso X N V).hom.base
        (((affineNormalizationDiagram X N).map f).base a) =
      ((gluedNormalizationModel X N).homOfLE
        (show (gluedNormalizationToBase X N) ⁻¹ᵁ U.val ≤
            (gluedNormalizationToBase X N) ⁻¹ᵁ V.val from by
          intro z hz
          exact (show U.val ≤ V.val from leOfHom f) hz)).base
        ((normalizationChartPreimageIso X N U).hom.base a) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    normalizationChartPreimageIso_naturality]

example (U : NonemptyAffineChart X) :
    (affineNormalizationDiagram X N).map (𝟙 U) ≫
      (normalizationChartPreimageIso X N U).hom =
      (normalizationChartPreimageIso X N U).hom := by
  rw [(affineNormalizationDiagram X N).map_id U, Category.id_comp]

example (f : U ⟶ V) (g : V ⟶ W) :
    (affineNormalizationDiagram X N).map f ≫
      (affineNormalizationDiagram X N).map g ≫
      (normalizationChartPreimageIso X N W).hom =
      (normalizationChartPreimageIso X N U).hom ≫
        (gluedNormalizationModel X N).homOfLE
          (show (gluedNormalizationToBase X N) ⁻¹ᵁ U.val ≤
              (gluedNormalizationToBase X N) ⁻¹ᵁ W.val from by
            intro z hz
            exact (show U.val ≤ W.val from leOfHom (f ≫ g)) hz) := by
  rw [← Category.assoc, ← Functor.map_comp]
  exact normalizationChartPreimageIso_naturality X N (f ≫ g)

example (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f =
      (normalizationChartPreimageIso X N U).hom ≫
        (gluedNormalizationModel X N).homOfLE
          (show (gluedNormalizationToBase X N) ⁻¹ᵁ U.val ≤
              (gluedNormalizationToBase X N) ⁻¹ᵁ V.val from by
            intro z hz
            exact (show U.val ≤ V.val from leOfHom f) hz) ≫
        (normalizationChartPreimageIso X N V).inv := by
  rw [← Category.assoc, ← normalizationChartPreimageIso_naturality X N f]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

example (f : U ⟶ V) :
    (normalizationChartPreimageIso X N U).inv ≫
      (affineNormalizationDiagram X N).map f =
      (gluedNormalizationModel X N).homOfLE
        (show (gluedNormalizationToBase X N) ⁻¹ᵁ U.val ≤
            (gluedNormalizationToBase X N) ⁻¹ᵁ V.val from by
          intro z hz
          exact (show U.val ≤ V.val from leOfHom f) hz) ≫
        (normalizationChartPreimageIso X N V).inv := by
  apply (cancel_mono (normalizationChartPreimageIso X N V).hom).mp
  simp only [Category.assoc, normalizationChartPreimageIso_naturality,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end RestrictionCompatibility

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_range,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_opensRange,
    `HodgeConjecture.CollisionFoundations.normalizationChartPreimageIso,
    `HodgeConjecture.CollisionFoundations.normalizationChartPreimageIso_hom_comp_inclusion,
    `HodgeConjecture.CollisionFoundations.normalizationChartPreimageIso_inv_comp_chart,
    `HodgeConjecture.CollisionFoundations.normalizationChartPreimageIso_hom_comp_restrict,
    `HodgeConjecture.CollisionFoundations.normalizationChartPreimageIso_naturality]
  unless declarations.length == 7 do
    throwError "Expected exactly 7 SP85 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP85 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
  logInfo "PASS SP85 audit registry: 7 distinct public declarations"
