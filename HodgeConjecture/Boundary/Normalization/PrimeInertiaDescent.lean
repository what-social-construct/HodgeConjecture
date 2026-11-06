module

public import HodgeConjecture.Boundary.Normalization.FixedRingLocalization
public import HodgeConjecture.Boundary.Normalization.LocalizationBridge

@[expose] public section

/-!
# Prime-inertia descent in a normalization diagram

This module composes the two local commutative-algebra bridges used at a
height-one normalization prime.  First, valuation-inertia containment is
converted to containment of the ring-theoretic prime inertia group.  Then
the fixed-prime-inertia input is descended through the selected fixed-ring
localizations.

The source ring is the literal full invariant ring `S^G` occurring in the
fixed-prime-inertia theorem.  Identifying it with the original affine base
is a separate step and requires the additional hypotheses recorded by
`baseEquivFullInvariantNormalizationRing`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace HodgeConjecture

noncomputable section

universe u

namespace NormalizationInertia

open AlgebraicGeometry

/-- At a height-one prime of a finite normal-closure normalization, prime
inertia containment in `H` and the fixed-prime-inertia input imply local
unramifiedness of the selected `H`-fixed branch over the full invariant
ring. -/
theorem normalizationFixedRing_isUnramifiedAt_of_primeInertia_le
    {B K N : Type u}
    [CommRing B] [Field K] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [FiniteDimensional K N] [IsNoetherianRing B]
    [Module.Finite B
      (NormalClosureNormalizationRing (B := B) (N := N))]
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] (hQ : Q.height = 1)
    (H : Subgroup (N ≃ₐ[K] N))
    (hIH : normalizationPrimeInertiaGroup
      (B := B) (K := K) Q ≤ H)
    (hI : NormalizationPrimeInertiaFixedRingUnramifiedAt
      (B := B) (K := K) Q) :
    InertiaFixedRingUnramifiedAt
      (A := FullInvariantNormalizationRing (B := B) (K := K) (N := N))
      (S := NormalClosureNormalizationRing (B := B) (N := N)) H Q := by
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let A := FullInvariantNormalizationRing (B := B) (K := K) (N := N)
  let I := normalizationPrimeInertiaGroup (B := B) (K := K) Q
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : Finite (N ≃ₐ[K] N) := by infer_instance
  letI : Module.Finite B A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite B A
  letI : Module.Finite A S :=
    Module.Finite.of_restrictScalars_finite B A S
  letI : IsIntegrallyClosed (FixedPoints.subalgebra A S H) := by
    let R := integralClosure B (IntermediateField.fixedField H)
    letI : IsIntegrallyClosed R :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    let eB : R ≃+* FixedSubgroupNormalizationRing (B := B) H :=
      (fixedFieldNormalizationEquivFixedRing (B := B) H).toRingEquiv
    let eA : FixedSubgroupNormalizationRing (B := B) H ≃+*
        FixedPoints.subalgebra A S H := RingEquiv.refl _
    exact IsIntegrallyClosed.of_equiv (eB.trans eA)
  constructor
  exact fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one
    I H hIH Q hQ hI

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
    {C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

/-- In a normalization diagram over a Noetherian base, valuation-inertia
containment in `H`, together with the literal fixed-prime-inertia input,
implies local unramifiedness of the selected `H`-fixed branch over `S^G`. -/
theorem fixedRing_isUnramifiedAt_of_valuationInertia_le
    [IsNoetherianRing B]
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (H : Subgroup C.normalClosure.galoisGroup)
    (hvaluation :
      CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing ≤ H)
    (hI : NormalizationPrimeInertiaFixedRingUnramifiedAt
      (B := B) (K := K) E.1.asIdeal) :
    InertiaFixedRingUnramifiedAt
      (A := FullInvariantNormalizationRing (B := B) (K := K) (N := N))
      (S := NormalClosureNormalizationRing (B := B) (N := N)) H
      E.1.asIdeal := by
  letI : E.1.asIdeal.IsPrime := E.1.isPrime
  letI : FiniteDimensional K N := C.normalClosure.finiteNormal
  letI : Module.Finite B
      (NormalClosureNormalizationRing (B := B) (N := N)) :=
    C.finiteNormalClosureModel
  exact normalizationFixedRing_isUnramifiedAt_of_primeInertia_le
    E.1.asIdeal E.2.1 H
    (D.normalizationPrimeInertia_le_of_valuationInertia_le_of_isNoetherianRing
      E H hvaluation)
    hI

end Diagram

end NormalizationInertia

end

end HodgeConjecture
