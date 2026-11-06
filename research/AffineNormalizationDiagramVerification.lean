module

import HodgeConjecture.Boundary.Normalization.GluedNormalization
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP84 regressions for the actual locally directed normalization-chart diagram.
Run with `lake env lean research/AffineNormalizationDiagramVerification.lean`.

The objects use the original generic-germ maps into one fixed ambient field.
The tests cover the existing restriction maps, functoriality, the structural
cocone over the original scheme, exact transition images, and pointwise
common-refinement witnesses. Gluing tests check the original charts form
an open cover, retain their actual transitions and structural maps, and
determine global morphisms. No finite-extension, normality, Noetherian, or
separatedness hypothesis is supplied. The exact audit registry checks every
new public API against the three standard Lean axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations

noncomputable section

universe u

section ActualObjects

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable (U V : NonemptyAffineChart X)

example : IsAffineOpen U.val := U.property.1

example : Nonempty U.val := inferInstance

example (W : X.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    (⟨W, hW, inferInstance⟩ : NonemptyAffineChart X).val = W := rfl

example (b : Γ(X, U.val)) :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    (affineNormalizationDiagram X N).obj U = normalizedAffineModel Γ(X, U.val) N := rfl

example (f : U ⟶ V) :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    letI : Algebra Γ(X, V.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V.val).hom).toAlgebra
    (affineNormalizationDiagram X N).map f =
      affineNormalizationRestriction V.val U.val N (leOfHom f) := rfl

example : (affineNormalizationBaseCocone X N).pt = X := rfl

example :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    (affineNormalizationBaseCocone X N).ι.app U =
      normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.fromSpec := rfl

example (a : (affineNormalizationDiagram X N).obj U) :
    ((affineNormalizationBaseCocone X N).ι.app U).base a ∈ U.val := by
  change ((affineNormalizationBaseCocone X N).ι.app U).base a ∈ (U.val : Set X)
  rw [← U.property.1.range_fromSpec]
  exact ⟨_, rfl⟩

end ActualObjects

section DiagramLaws

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable (U V W T : NonemptyAffineChart X)

example : (affineNormalizationDiagram X N).map (𝟙 U) = 𝟙 _ :=
  (affineNormalizationDiagram X N).map_id U

example (f : U ⟶ V) (g : V ⟶ W) :
    (affineNormalizationDiagram X N).map (f ≫ g) =
      (affineNormalizationDiagram X N).map f ≫ (affineNormalizationDiagram X N).map g :=
  (affineNormalizationDiagram X N).map_comp f g

example (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ T) :
    ((affineNormalizationDiagram X N).map f ≫ (affineNormalizationDiagram X N).map g) ≫
      (affineNormalizationDiagram X N).map h =
      (affineNormalizationDiagram X N).map ((f ≫ g) ≫ h) := by
  simp only [Functor.map_comp]

example (f : U ⟶ V) (g : U ⟶ W) (h : V ⟶ T) (k : W ⟶ T) :
    (affineNormalizationDiagram X N).map f ≫ (affineNormalizationDiagram X N).map h =
      (affineNormalizationDiagram X N).map g ≫ (affineNormalizationDiagram X N).map k := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

example (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫
      (affineNormalizationBaseCocone X N).ι.app V =
      (affineNormalizationBaseCocone X N).ι.app U :=
  (affineNormalizationBaseCocone X N).w f

example (f : U ⟶ V) (g : V ⟶ W) :
    (affineNormalizationDiagram X N).map f ≫ (affineNormalizationDiagram X N).map g ≫
      (affineNormalizationBaseCocone X N).ι.app W =
      (affineNormalizationBaseCocone X N).ι.app U := by
  rw [(affineNormalizationBaseCocone X N).w g, (affineNormalizationBaseCocone X N).w f]

example (f : U ⟶ V) : IsOpenImmersion ((affineNormalizationDiagram X N).map f) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  infer_instance

example (f : U ⟶ V) : Mono ((affineNormalizationDiagram X N).map f) := inferInstance

example (f : U ⟶ V) : Function.Injective ((affineNormalizationDiagram X N).map f).base :=
  ((affineNormalizationDiagram X N).map f).isOpenEmbedding.injective

example (f : U ⟶ V) :
    Set.range ((affineNormalizationDiagram X N).map f).base =
      ((affineNormalizationBaseCocone X N).ι.app V).base ⁻¹' (U.val : Set X) :=
  affineNormalizationDiagram_range X N f

example (f : U ⟶ V) (a : (affineNormalizationDiagram X N).obj V) :
    a ∈ Set.range ((affineNormalizationDiagram X N).map f).base ↔
      ((affineNormalizationBaseCocone X N).ι.app V).base a ∈ U.val := by
  rw [affineNormalizationDiagram_range]
  rfl

end DiagramLaws

section CommonRefinements

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example : ((affineNormalizationDiagram X N) ⋙ Scheme.forget).IsLocallyDirected := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  infer_instance

example {U V T : NonemptyAffineChart X} (f : U ⟶ T) (g : V ⟶ T)
    (a : (affineNormalizationDiagram X N).obj U)
    (b : (affineNormalizationDiagram X N).obj V)
    (hab : ((affineNormalizationDiagram X N).map f).base a =
      ((affineNormalizationDiagram X N).map g).base b) :
    ∃ (W : NonemptyAffineChart X) (i : W ⟶ U) (j : W ⟶ V)
      (w : (affineNormalizationDiagram X N).obj W),
      ((affineNormalizationDiagram X N).map i).base w = a ∧
        ((affineNormalizationDiagram X N).map j).base w = b :=
  ((affineNormalizationDiagram X N) ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected
    f g a b hab

example {U V T : NonemptyAffineChart X} (f : U ⟶ T) (g : V ⟶ T)
    (a : (affineNormalizationDiagram X N).obj U)
    (b : (affineNormalizationDiagram X N).obj V)
    (hab : ((affineNormalizationDiagram X N).map f).base a =
      ((affineNormalizationDiagram X N).map g).base b) :
    ∃ (W : NonemptyAffineChart X) (i : W ⟶ U) (j : W ⟶ V)
      (w : (affineNormalizationDiagram X N).obj W),
      W.val ≤ U.val ⊓ V.val ∧
        ((affineNormalizationDiagram X N).map i).base w = a ∧
        ((affineNormalizationDiagram X N).map j).base w = b := by
  obtain ⟨W, i, j, w, hwU, hwV⟩ :=
    ((affineNormalizationDiagram X N) ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected
      f g a b hab
  exact ⟨W, i, j, w, le_inf (leOfHom i) (leOfHom j), hwU, hwV⟩

end CommonRefinements

section GluedCharts

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example : HasColimit (affineNormalizationDiagram X N) := inferInstance

example : gluedNormalizationModel X N = colimit (affineNormalizationDiagram X N) := rfl

example (U : NonemptyAffineChart X) :
    normalizationChartToGlued X N U = colimit.ι (affineNormalizationDiagram X N) U := rfl

example (U : NonemptyAffineChart X) : IsOpenImmersion (normalizationChartToGlued X N U) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  infer_instance

example (U : NonemptyAffineChart X) : Mono (normalizationChartToGlued X N U) := inferInstance

example : (gluedNormalizationOpenCover X N).I₀ = NonemptyAffineChart X := rfl

example (U : NonemptyAffineChart X) :
    (gluedNormalizationOpenCover X N).X U = (affineNormalizationDiagram X N).obj U := rfl

example (U : NonemptyAffineChart X) :
    (gluedNormalizationOpenCover X N).f U = normalizationChartToGlued X N U := rfl

example (z : gluedNormalizationModel X N) :
    ∃ (U : NonemptyAffineChart X) (a : (affineNormalizationDiagram X N).obj U),
      (normalizationChartToGlued X N U).base a = z :=
  (gluedNormalizationOpenCover X N).exists_eq z

example (U : NonemptyAffineChart X) :
    normalizationChartToGlued X N U ≫ gluedNormalizationToBase X N =
      (affineNormalizationBaseCocone X N).ι.app U :=
  normalizationChartToGlued_comp_toBase X N U

example (U : NonemptyAffineChart X) (a : (affineNormalizationDiagram X N).obj U) :
    (gluedNormalizationToBase X N).base ((normalizationChartToGlued X N U).base a) =
      ((affineNormalizationBaseCocone X N).ι.app U).base a := by
  rw [← Scheme.Hom.comp_apply, normalizationChartToGlued_comp_toBase]
  rfl

example {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫ normalizationChartToGlued X N V =
      normalizationChartToGlued X N U :=
  normalizationChartToGlued_naturality X N f

example {U V : NonemptyAffineChart X}
    (a : (affineNormalizationDiagram X N).obj U)
    (b : (affineNormalizationDiagram X N).obj V) :
    (normalizationChartToGlued X N U).base a =
        (normalizationChartToGlued X N V).base b ↔
      ∃ (W : NonemptyAffineChart X) (f : W ⟶ U) (g : W ⟶ V)
        (w : (affineNormalizationDiagram X N).obj W),
        ((affineNormalizationDiagram X N).map f).base w = a ∧
        ((affineNormalizationDiagram X N).map g).base w = b :=
  normalizationChartToGlued_eq_iff X N a b

example {U V W : NonemptyAffineChart X} (f : W ⟶ U) (g : W ⟶ V)
    (w : (affineNormalizationDiagram X N).obj W) :
    (normalizationChartToGlued X N U).base (((affineNormalizationDiagram X N).map f).base w) =
      (normalizationChartToGlued X N V).base (((affineNormalizationDiagram X N).map g).base w) :=
  (normalizationChartToGlued_eq_iff X N _ _).mpr ⟨W, f, g, w, rfl, rfl⟩

example {Y : Scheme.{u}} (f g : gluedNormalizationModel X N ⟶ Y)
    (h : ∀ U : NonemptyAffineChart X,
      normalizationChartToGlued X N U ≫ f = normalizationChartToGlued X N U ≫ g) : f = g :=
  gluedNormalization_hom_ext X N f g h

example (μ : gluedNormalizationModel X N ⟶ X)
    (hμ : ∀ U : NonemptyAffineChart X,
      normalizationChartToGlued X N U ≫ μ = (affineNormalizationBaseCocone X N).ι.app U) :
    μ = gluedNormalizationToBase X N := by
  apply gluedNormalization_hom_ext X N
  intro U
  rw [hμ U, normalizationChartToGlued_comp_toBase]

example (U : NonemptyAffineChart X) :
    letI : Algebra Γ(X, U.val) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
    normalizationChartToGlued X N U ≫ gluedNormalizationToBase X N =
      normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.fromSpec :=
  normalizationChartToGlued_comp_toBase X N U

end GluedCharts

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.NonemptyAffineChart,
    `HodgeConjecture.CollisionFoundations.nonemptyAffineChart_nonempty,
    `HodgeConjecture.CollisionFoundations.affineNormalizationDiagram,
    `HodgeConjecture.CollisionFoundations.affineNormalizationBaseCocone,
    `HodgeConjecture.CollisionFoundations.affineNormalizationDiagram_isOpenImmersion,
    `HodgeConjecture.CollisionFoundations.affineNormalizationDiagram_range,
    `HodgeConjecture.CollisionFoundations.affineNormalizationDiagram_isLocallyDirected,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationModel,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_isOpenImmersion,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationOpenCover,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationToBase,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_comp_toBase,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_naturality,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_eq_iff,
    `HodgeConjecture.CollisionFoundations.gluedNormalization_hom_ext]
  unless declarations.length == 16 do
    throwError "Expected exactly 16 SP84 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP84 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
  logInfo "PASS SP84 audit registry: 16 distinct public declarations"
