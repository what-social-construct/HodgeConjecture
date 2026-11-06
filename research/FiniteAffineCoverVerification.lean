module

import HodgeConjecture.Boundary
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP70 regressions for canonical finite affine normalization covers and their
full-visible boundary ideals. Run with
`lake env lean research/FiniteAffineCoverVerification.lean`.

The boundary umbrella import checks public availability. The affine identification
uses integral normal models, independently of étaleness. The étale test
transports an explicit instance; it does not infer normality from étaleness.
All new public declarations have an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.NormalizationInertia

noncomputable section

universe u

section Algebra

variable {B A E : Type u}
variable [CommRing B] [CommRing A] [CommRing E]
variable [Algebra B A] [Algebra B E] [Algebra A E]
variable [IsScalarTower B A E] [IsIntegralClosure A A E]
variable [Algebra.IsIntegral B A]

-- Neither Noetherianity nor étaleness is needed for the identification.
example : Function.Surjective
    (normalizationToIntermediate (B := B) (A := A) (E := E)) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.Etale B A := inferInstance
  exact normalizationToIntermediate_surjective

example (t : normalizedCoordinateRing B E) :
    normalizationIntermediateEquiv (B := B) (A := A) (E := E) t =
      normalizationToIntermediate (B := B) (A := A) (E := E) t := rfl

example : (intermediateNormalizationIso (B := B) (A := A) (E := E)).hom =
    intermediateToNormalization (B := B) (A := A) (E := E) :=
  intermediateNormalizationIso_hom

example :
    (intermediateNormalizationIso (B := B) (A := A) (E := E)).hom ≫
        normalizedModelToBase B E =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
  rw [intermediateNormalizationIso_hom (B := B) (A := A) (E := E)]
  exact intermediateToNormalization_comp_toBase (B := B) (A := A) (E := E)

example : Function.Surjective
    (intermediateToNormalization (B := B) (A := A) (E := E)).base :=
  intermediateToNormalization_base_surjective

example [Algebra.Etale B A] : Algebra.Etale B (normalizedCoordinateRing B E) :=
  normalizedCoordinateRing_etale (A := A)

example [Module.Finite B A] : Module.Finite B (normalizedCoordinateRing B E) :=
  normalizedCoordinateRing_finite (A := A)

end Algebra

section Visibility

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)
variable (hVisible : Function.Surjective j.base)

example (g : C.GaloisGroup) : pulledBackConjugateVisibleOpen C g = Set.univ :=
  pulledBackConjugateVisibleOpen_eq_univ_of_surjective C hVisible g

example (g : C.GaloisGroup) : pulledBackConjugateBoundary C g = ∅ :=
  pulledBackConjugateBoundary_eq_empty_of_surjective C hVisible g

example (g : C.GaloisGroup) : pulledBackConjugateBoundaryIdeal C g = ⊤ := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact pulledBackConjugateBoundaryIdeal_eq_top_of_surjective C hVisible g

-- The nontrivial-subgroup premise is essential: the trivial group moves no sheet.
example : movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) ⊥ = ⊥ := by
  simp [movingBoundaryIdeal]

example [PerfectField K] (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I = ⊤ :=
  movingBoundaryIdeal_eq_top_of_surjective C hVisible I hI

example [PerfectField K] (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    fixedMovingBoundaryIdeal C I = ⊤ :=
  fixedMovingBoundaryIdeal_eq_top_of_surjective C hVisible I hI

example [PerfectField K] : ConjugateBoundarySeparation C := by
  fail_if_success have _ : IsFractionRing B K := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact conjugateBoundarySeparation_of_surjective C hVisible

end Visibility

section ConstructedCover

variable {B K L N A S : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [CommRing A] [Algebra B A] [Algebra A L]
variable [IsScalarTower B A L] [IsFractionRing A L] [IsIntegrallyClosed A]
variable [CommRing S] [Algebra B S] [Algebra S N]
variable [IsScalarTower B S N] [IsFractionRing S N] [IsIntegrallyClosed S]
variable [Module.Finite B A] [Module.Finite B S]
variable (D : NormalClosureData K L N)

example :
    (normalizedCoverOfFiniteNormalAffineModels (B := B) (A := A) (S := S) D).normalClosure = D :=
  rfl

-- Finiteness is derived from the actual affine models, not assumed for integral closures.
example : Module.Finite B (IntermediateNormalizationRing (B := B) (L := L)) :=
  (normalizedCoverOfFiniteNormalAffineModels (B := B) (A := A) (S := S) D).finiteIntermediateModel

example : Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N)) :=
  (normalizedCoverOfFiniteNormalAffineModels (B := B) (A := A) (S := S) D).finiteNormalClosureModel

example : IsOpenImmersion
    (intermediateToNormalization (B := B) (A := A) (E := L)) :=
  (normalizedCoverOfFiniteNormalAffineModels (B := B) (A := A) (S := S) D).visibleOpen

example [PerfectField K] : ConjugateBoundarySeparation
    (normalizedCoverOfFiniteNormalAffineModels (B := B) (A := A) (S := S) D) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.Etale B A := inferInstance
  exact conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels
    (B := B) (A := A) (S := S) D

end ConstructedCover

-- A finite normal field extension supplies the marked datum as well as both affine models.
-- This regression constructs the datum; it does not postulate a NormalizedCover.
example (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Normal K L] [PerfectField K] :
    ∃ C : NormalizedCover (B := K) (K := K) (L := L) (N := L)
      (Spec (.of L)) (intermediateToNormalization (B := K) (A := L) (E := L)),
      ConjugateBoundarySeparation C := by
  have hClosure : IsNormalClosure K L L := by
    apply Algebra.IsAlgebraic.isNormalClosure_iff.mpr
    refine ⟨Normal.splits inferInstance, ?_⟩
    apply top_unique
    have hRange : (AlgHom.id K L).fieldRange = ⊤ :=
      AlgHom.fieldRange_eq_top.mpr Function.surjective_id
    rw [← hRange]
    exact (AlgHom.id K L).fieldRange_le_normalClosure
  let D : NormalClosureData K L L :=
    ⟨AlgHom.id K L, hClosure, inferInstance, inferInstance⟩
  exact ⟨normalizedCoverOfFiniteNormalAffineModels (B := K) (A := L) (S := L) D,
    conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels
      (B := K) (A := L) (S := L) D⟩

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.normalizationToIntermediate_surjective,
      `HodgeConjecture.CollisionFoundations.normalizationIntermediateEquiv,
      `HodgeConjecture.CollisionFoundations.normalizationIntermediateEquiv_toAlgHom,
      `HodgeConjecture.CollisionFoundations.intermediateNormalizationIso,
      `HodgeConjecture.CollisionFoundations.intermediateNormalizationIso_hom,
      `HodgeConjecture.CollisionFoundations.intermediateToNormalization_isIso,
      `HodgeConjecture.CollisionFoundations.intermediateToNormalization_base_surjective,
      `HodgeConjecture.CollisionFoundations.normalizedCoordinateRing_etale,
      `HodgeConjecture.CollisionFoundations.normalizedCoordinateRing_finite,
      `HodgeConjecture.NormalizationInertia.normalizedCoverOfFiniteNormalAffineModels,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels,
      `HodgeConjecture.NormalizationInertia.pulledBackConjugateVisibleOpen_eq_univ_of_surjective,
      `HodgeConjecture.NormalizationInertia.pulledBackConjugateBoundary_eq_empty_of_surjective,
      `HodgeConjecture.NormalizationInertia.pulledBackConjugateBoundaryIdeal_eq_top_of_surjective,
      `HodgeConjecture.NormalizationInertia.movingBoundaryIdeal_eq_top_of_surjective,
      `HodgeConjecture.NormalizationInertia.fixedMovingBoundaryIdeal_eq_top_of_surjective,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_of_surjective] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
