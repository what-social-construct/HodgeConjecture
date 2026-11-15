module

public import HodgeConjecture.Boundary.Normalization.FixedRingLocalization
public import HodgeConjecture.Boundary.Normalization.PrimeInertia

@[expose] public section

/-!
# The full invariant normalization as a height-one DVR base

For a finite Galois normal-closure field, the full invariant ring of the
normalization is the integral closure of the affine base in its fraction
field. This gives normality and the required fraction-field identification
without assuming the original affine base is normal.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

variable {B K N : Type u}
variable [CommRing B] [Field K] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K N] [Algebra B N] [IsScalarTower B K N]
variable [FiniteDimensional K N] [IsGalois K N]

/-- The full Galois-invariant normalization is the integral closure of `B`
inside its fraction field `K`. -/
def integralClosureEquivFullInvariantNormalization :
    integralClosure B K ≃ₐ[B]
      FullInvariantNormalizationRing (B := B) (K := K) (N := N) := by
  let eFixed :
      IntermediateField.fixedField
          (⊤ : Subgroup (N ≃ₐ[K] N)) ≃ₐ[K] K :=
    (IntermediateField.equivOfEq
      (IsGalois.fixedField_top (F := K) (E := N))).trans
        (IntermediateField.botEquiv K N)
  let eClosure :
      integralClosure B
          (IntermediateField.fixedField
            (⊤ : Subgroup (N ≃ₐ[K] N))) ≃ₐ[B]
        integralClosure B K :=
    (eFixed.restrictScalars B).mapIntegralClosure
  exact eClosure.symm.trans <|
    fixedFieldNormalizationEquivFixedRing
      (B := B) (⊤ : Subgroup (N ≃ₐ[K] N))

/-- The full invariant normalization is normal even when `B` itself is not. -/
theorem fullInvariantNormalizationRing_isIntegrallyClosed :
    IsIntegrallyClosed
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : IsIntegrallyClosed (integralClosure B K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  exact IsIntegrallyClosed.of_equiv
    (integralClosureEquivFullInvariantNormalization
      (B := B) (K := K) (N := N)).toRingEquiv

/-- The embedding of full invariants into their fraction field, constructed
through the integral-closure equivalence. -/
def fullInvariantNormalizationToFractionField :
    FullInvariantNormalizationRing (B := B) (K := K) (N := N) →ₐ[B] K :=
  (integralClosure B K).val.comp
    (integralClosureEquivFullInvariantNormalization
      (B := B) (K := K) (N := N)).symm.toAlgHom

/-- `K` is the fraction field of the full invariant normalization. -/
theorem fullInvariantNormalizationRing_isFractionRing :
    letI : Algebra
        (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) K :=
      (fullInvariantNormalizationToFractionField
        (B := B) (K := K) (N := N)).toAlgebra
    IsFractionRing
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) K := by
  letI : Algebra
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) K :=
    (fullInvariantNormalizationToFractionField
      (B := B) (K := K) (N := N)).toAlgebra
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : IsFractionRing (integralClosure B K) K :=
    integralClosure.isFractionRing_of_finite_extension K K
  exact IsFractionRing.of_ringEquiv_left
    (integralClosureEquivFullInvariantNormalization
      (B := B) (K := K) (N := N)).symm.toRingEquiv
    (fun _ ↦ rfl)

/-- Finite normalization makes the full invariant ring Noetherian. -/
theorem fullInvariantNormalizationRing_isNoetherian
    [IsNoetherianRing B]
    [Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N))] :
    IsNoetherianRing
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) := by
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let A := FullInvariantNormalizationRing (B := B) (K := K) (N := N)
  letI : Module.Finite B A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  exact IsNoetherianRing.of_finite B A

/-- A height-one normalization prime contracts to height one in the full
invariant normalization. -/
theorem fullInvariantNormalizationRing_primeHeight_under_eq_one
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] (hQ : Q.height = 1) :
    (Q.under
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N))).height = 1 := by
  letI : Finite (N ≃ₐ[K] N) := inferInstance
  exact fixedPoints_primeHeight_under_eq_one (A := B)
    (⊤ : Subgroup (N ≃ₐ[K] N)) Q hQ

/-- A height-one prime of the full invariant normalization has a DVR
localization, with no normality assumption on `B`. -/
theorem fullInvariantNormalizationRing_localization_isDiscreteValuationRing
    [IsNoetherianRing B]
    [Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N))]
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] (hQ : Q.height = 1) :
    IsDiscreteValuationRing
      (Localization.AtPrime
        (Q.under (FullInvariantNormalizationRing (B := B) (K := K) (N := N)))) := by
  letI : IsNoetherianRing
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) :=
    fullInvariantNormalizationRing_isNoetherian (B := B) (K := K) (N := N)
  letI : IsIntegrallyClosed
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N)) :=
    fullInvariantNormalizationRing_isIntegrallyClosed (B := B) (K := K) (N := N)
  exact localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one
    (Q.under (FullInvariantNormalizationRing (B := B) (K := K) (N := N)))
    (fullInvariantNormalizationRing_primeHeight_under_eq_one
      (B := B) (K := K) (N := N) Q hQ)

end

end HodgeConjecture.NormalizationInertia
