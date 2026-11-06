module

public import HodgeConjecture.Boundary.Normalization.FullVisibleBoundary
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

/-!
# Finite normal affine models as actual normalization covers

An integral affine algebra, integrally closed in the chosen overring, is
canonically its base's integral closure there.  The resulting scheme
isomorphism is the existing `intermediateToNormalization`, not an independently
supplied visible-open morphism.  Finite normal affine models for the intermediate
and normal-closure fields therefore construct the existing `NormalizedCover`.

Étaleness transports along this canonical identification.  The ring hypotheses
here are explicit; constructing these affine models from a global smooth
projective finite étale cover is a separate geometric operation.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace CollisionFoundations

section IntegralModel

variable {B A E : Type u}
variable [CommRing B] [CommRing A] [CommRing E]
variable [Algebra B A] [Algebra B E] [Algebra A E]
variable [IsScalarTower B A E] [IsIntegralClosure A A E]
variable [Algebra.IsIntegral B A]

/-- An integral intermediate algebra fills the entire normalization ring. -/
theorem normalizationToIntermediate_surjective :
    Function.Surjective
      (normalizationToIntermediate (B := B) (A := A) (E := E)) := by
  intro a
  refine ⟨⟨algebraMap A E a,
    IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := B) a)⟩, ?_⟩
  apply IsIntegralClosure.algebraMap_injective A A E
  simp

/-- The canonical normalization map is an algebra isomorphism for an integral
intermediate algebra integrally closed in the overring. -/
def normalizationIntermediateEquiv : normalizedCoordinateRing B E ≃ₐ[B] A :=
  AlgEquiv.ofBijective
    (normalizationToIntermediate (B := B) (A := A) (E := E))
    ⟨normalizationToIntermediate_injective (A := A),
      normalizationToIntermediate_surjective⟩

@[simp]
theorem normalizationIntermediateEquiv_toAlgHom :
    (normalizationIntermediateEquiv (B := B) (A := A) (E := E)).toAlgHom =
      normalizationToIntermediate (B := B) (A := A) (E := E) := rfl

/-- The actual affine scheme is canonically its base's normalization. -/
def intermediateNormalizationIso :
    Spec (.of A) ≅ normalizedAffineModel B E :=
  Scheme.Spec.mapIso
    (normalizationIntermediateEquiv (B := B) (A := A) (E := E)).toRingEquiv.toCommRingCatIso.op

@[simp]
theorem intermediateNormalizationIso_hom :
    (intermediateNormalizationIso (B := B) (A := A) (E := E)).hom =
      intermediateToNormalization (B := B) (A := A) (E := E) := rfl

/-- The canonical intermediate morphism is an isomorphism when its algebra
is integral over the base. -/
theorem intermediateToNormalization_isIso :
    IsIso (intermediateToNormalization (B := B) (A := A) (E := E)) := by
  rw [← intermediateNormalizationIso_hom]
  infer_instance

/-- In particular, the canonical affine model covers the whole normalization. -/
theorem intermediateToNormalization_base_surjective :
    Function.Surjective
      (intermediateToNormalization (B := B) (A := A) (E := E)).base := by
  letI := intermediateToNormalization_isIso (B := B) (A := A) (E := E)
  exact (ConcreteCategory.bijective_of_isIso _).surjective

/-- Étaleness is retained by the canonical normalization identification. -/
theorem normalizedCoordinateRing_etale [Algebra.Etale B A] :
    Algebra.Etale B (normalizedCoordinateRing B E) :=
  Algebra.Etale.of_equiv
    (normalizationIntermediateEquiv (B := B) (A := A) (E := E)).symm

end IntegralModel

section FiniteModel

variable {B A E : Type u}
variable [CommRing B] [CommRing A] [CommRing E]
variable [Algebra B A] [Algebra B E] [Algebra A E]
variable [IsScalarTower B A E] [IsIntegralClosure A A E]
variable [Module.Finite B A]

include A in
/-- Finiteness of the actual intermediate affine algebra gives finiteness of
the normalization through the canonical algebra isomorphism. -/
theorem normalizedCoordinateRing_finite :
    Module.Finite B (normalizedCoordinateRing B E) :=
  Module.Finite.equiv
    (normalizationIntermediateEquiv (B := B) (A := A) (E := E)).symm.toLinearEquiv

end FiniteModel

end CollisionFoundations

namespace NormalizationInertia

section FiniteNormalAffineModels

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

/-- Actual finite normal affine algebras in the two chosen fraction fields
construct a normalized cover with its canonical, fully visible affine model.
No finiteness or openness of the normalization is assumed separately. -/
def normalizedCoverOfFiniteNormalAffineModels
    (D : CollisionFoundations.NormalClosureData K L N) :
    NormalizedCover (B := B) (K := K) (L := L) (N := N)
      (Spec (.of A))
      (CollisionFoundations.intermediateToNormalization
        (B := B) (A := A) (E := L)) where
  normalClosure := D
  finiteIntermediateModel :=
    CollisionFoundations.normalizedCoordinateRing_finite (A := A)
  finiteNormalClosureModel :=
    CollisionFoundations.normalizedCoordinateRing_finite (A := S)
  visibleOpen := by
    letI := CollisionFoundations.intermediateToNormalization_isIso
      (B := B) (A := A) (E := L)
    infer_instance

omit [IsFractionRing B K] in
/-- The actual finite normal affine models give boundary separation because
their canonical visible-open morphism is an isomorphism. -/
theorem conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels
    (D : CollisionFoundations.NormalClosureData K L N) :
    ConjugateBoundarySeparation
      (normalizedCoverOfFiniteNormalAffineModels
        (B := B) (A := A) (S := S) D) :=
  conjugateBoundarySeparation_of_surjective _
    (CollisionFoundations.intermediateToNormalization_base_surjective
      (B := B) (A := A) (E := L))

end FiniteNormalAffineModels

end NormalizationInertia

end

end HodgeConjecture
