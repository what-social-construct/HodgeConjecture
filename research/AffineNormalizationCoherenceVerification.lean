import HodgeConjecture.Boundary.Normalization.AffineNormalizationCoherence
import HodgeConjecture.Boundary.Normalization.AffineNormalizationOpenImmersion
import Lean.Util.CollectAxioms

/-!
SP83 regressions for actual affine-normalization restriction coherence.
Run with `lake env lean research/AffineNormalizationCoherenceVerification.lean`.

The identity, chain, and common-subopen tests retain the same ambient field
and its original generic-germ scalar maps. The generic coherence statements
do not assume affine opens, normality, finite field extensions, or Noetherian
geometry. Principal image tests use the structural morphism to the original
scheme, rather than an independently selected affine model of the base.
The non-affine intersection examples test only formal restriction-chain
coherence; genuine inverse-image identification is tested separately for
nested affine opens. All ten new public APIs receive an exact, unique
standard-three-axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations

noncomputable section

universe u

section ActualCoherence

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V W : X.Opens) [Nonempty U] [Nonempty V] [Nonempty W]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    affineNormalizationRestriction U U N le_rfl = 𝟙 _ := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  exact affineNormalizationRestriction_self U N

example (hUU : U ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    affineNormalizationRestriction U U N hUU = 𝟙 _ :=
  affineNormalizationRestriction_self U N

example (hVU : V ≤ U) (hWV : W ≤ V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    affineNormalizationRestriction V W N hWV ≫
      affineNormalizationRestriction U V N hVU =
      affineNormalizationRestriction U W N (hWV.trans hVU) :=
  affineNormalizationRestriction_trans U V W N hVU hWV

example (T : X.Opens) [Nonempty T]
    (hVU : V ≤ U) (hWV : W ≤ V) (hTW : T ≤ W) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    letI : Algebra Γ(X, T) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField T).hom).toAlgebra
    (affineNormalizationRestriction W T N hTW ≫
      affineNormalizationRestriction V W N hWV) ≫
      affineNormalizationRestriction U V N hVU =
      affineNormalizationRestriction U T N ((hTW.trans hWV).trans hVU) := by
  rw [affineNormalizationRestriction_trans, affineNormalizationRestriction_trans]

example (T : X.Opens) [Nonempty T]
    (hVU : V ≤ U) (hWU : W ≤ U) (hTV : T ≤ V) (hTW : T ≤ W) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    letI : Algebra Γ(X, T) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField T).hom).toAlgebra
    affineNormalizationRestriction V T N hTV ≫ affineNormalizationRestriction U V N hVU =
      affineNormalizationRestriction W T N hTW ≫ affineNormalizationRestriction U W N hWU :=
  affineNormalizationRestriction_diamond U V W N T hVU hWU hTV hTW

-- The coefficient map still goes through the original generic germ.
example (b : Γ(X, U)) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    algebraMap Γ(X, U) N b =
      algebraMap X.functionField N ((X.germToFunctionField U).hom b) := rfl

example (hVU : V ≤ U) (hWV : W ≤ V) (b : Γ(X, U)) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    algebraMap Γ(X, U) N b =
      algebraMap Γ(X, W) N
        ((X.presheaf.map (homOfLE hWV).op).hom
          ((X.presheaf.map (homOfLE hVU).op).hom b)) := by
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X, W) :=
    (X.presheaf.map (homOfLE hWV).op).hom.toAlgebra
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, W) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, V) N :=
    sectionRestriction_ambientScalarTower U V N hVU
  letI : IsScalarTower Γ(X, V) Γ(X, W) N :=
    sectionRestriction_ambientScalarTower V W N hWV
  exact (IsScalarTower.algebraMap_apply Γ(X, U) Γ(X, V) N b).trans
    (IsScalarTower.algebraMap_apply Γ(X, V) Γ(X, W) N
      (algebraMap Γ(X, U) Γ(X, V) b))

end ActualCoherence

section NonemptyOverlaps

variable {X : Scheme.{u}} [IsIntegral X]

local instance coherenceVerificationInfNonempty
    (A B : X.Opens) [Nonempty A] [Nonempty B] : Nonempty (A ⊓ B : X.Opens) := by
  simpa using nonempty_preirreducible_inter A.isOpen B.isOpen
    (by simpa using (inferInstance : Nonempty A))
    (by simpa using (inferInstance : Nonempty B))

variable (U V W : X.Opens) [Nonempty U] [Nonempty V] [Nonempty W]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example : Nonempty (U ⊓ V : X.Opens) := inferInstance

example : Nonempty ((U ⊓ V) ⊓ W : X.Opens) := inferInstance

example (hVU : V ≤ U) (hWU : W ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    letI : Algebra Γ(X, V ⊓ W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField (V ⊓ W)).hom).toAlgebra
    affineNormalizationRestriction V (V ⊓ W) N inf_le_left ≫
      affineNormalizationRestriction U V N hVU =
      affineNormalizationRestriction W (V ⊓ W) N inf_le_right ≫
        affineNormalizationRestriction U W N hWU :=
  affineNormalizationRestriction_diamond U V W N (V ⊓ W)
    hVU hWU inf_le_left inf_le_right

example :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, U ⊓ V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField (U ⊓ V)).hom).toAlgebra
    letI : Algebra Γ(X, U ⊓ W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField (U ⊓ W)).hom).toAlgebra
    letI : Algebra Γ(X, (U ⊓ V) ⊓ W) N :=
      ((algebraMap X.functionField N).comp
        (X.germToFunctionField ((U ⊓ V) ⊓ W)).hom).toAlgebra
    affineNormalizationRestriction (U ⊓ V) ((U ⊓ V) ⊓ W) N inf_le_left ≫
      affineNormalizationRestriction U (U ⊓ V) N inf_le_left =
      affineNormalizationRestriction (U ⊓ W) ((U ⊓ V) ⊓ W) N
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ≫
        affineNormalizationRestriction U (U ⊓ W) N inf_le_left :=
  affineNormalizationRestriction_diamond U (U ⊓ V) (U ⊓ W) N ((U ⊓ V) ⊓ W)
    inf_le_left inf_le_left inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

end NonemptyOverlaps

section PrincipalImages

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V N hVU ≫
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec) =
      normalizedModelToBase Γ(X, V) N ≫ hV.fromSpec :=
  affineNormalizationRestriction_comp_toX U V N hVU hU hV

example (hU : IsAffineOpen U) (f : Γ(X, U)) [Nonempty (X.basicOpen f)] :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, X.basicOpen f) N :=
      ((algebraMap X.functionField N).comp
        (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
    Set.range (affineNormalizationRestriction U (X.basicOpen f) N (X.basicOpen_le f)).base =
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base ⁻¹'
        (X.basicOpen f : Set X) :=
  affineNormalizationRestriction_basicOpen_range U N hU f

example (hVU : V ≤ U) (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : V = X.basicOpen f) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    Set.range (affineNormalizationRestriction U V N hVU).base =
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base ⁻¹' (V : Set X) :=
  affineNormalizationRestriction_range_of_eq_basicOpen U V N hVU hU f hV

example (hVU : V ≤ U) (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : V = X.basicOpen f) :
    IsOpenImmersion (affineNormalizationRestriction U V N hVU) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  exact affineNormalizationRestriction_isOpenImmersion_of_eq_basicOpen U V N hVU hU f hV

-- The unit principal presentation recovers the original chart, rather
-- than a second chosen normalization object.
example (hU : IsAffineOpen U) : IsOpenImmersion
    (affineNormalizationRestriction U U N le_rfl) :=
  affineNormalizationRestriction_isOpenImmersion_of_eq_basicOpen U U N le_rfl hU
    (1 : Γ(X, U)) (X.basicOpen_one).symm

end PrincipalImages

section ArbitraryAffineImages

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Injective (affineNormalizationRestriction U V N hVU).base :=
  affineNormalizationRestriction_injective U V N hVU hU hV

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsOpenImmersion (affineNormalizationRestriction U V N hVU) := by
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  exact affineNormalizationRestriction_isOpenImmersion U V N hVU hU hV

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    Set.range (affineNormalizationRestriction U V N hVU).base =
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base ⁻¹' (V : Set X) :=
  affineNormalizationRestriction_range U V N hVU hU hV

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Mono (affineNormalizationRestriction U V N hVU) := by
  letI : IsOpenImmersion (affineNormalizationRestriction U V N hVU) :=
    affineNormalizationRestriction_isOpenImmersion U V N hVU hU hV
  infer_instance

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    ∀ a : normalizedAffineModel Γ(X, U) N,
      a ∈ Set.range (affineNormalizationRestriction U V N hVU).base ↔
        (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base a ∈ V := by
  rw [affineNormalizationRestriction_range U V N hVU hU hV]
  exact fun _ => Iff.rfl

end ArbitraryAffineImages

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_self,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_trans,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_diamond,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_comp_toX,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_basicOpen_range,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_range_of_eq_basicOpen,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_isOpenImmersion_of_eq_basicOpen,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_injective,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_isOpenImmersion,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_range]
  unless declarations.length == 10 do
    throwError "Expected exactly 10 SP83 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP83 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP83 audit registry: 10 distinct public declarations"
