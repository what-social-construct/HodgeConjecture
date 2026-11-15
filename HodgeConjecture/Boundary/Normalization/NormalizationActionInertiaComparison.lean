module

public import HodgeConjecture.Boundary.Normalization.NormalizationActionComparison

@[expose] public section

/-!
# Inertia under the two normalization actions

The project's normal-closure action and Mathlib's integral-closure Galois
action are equal as action structures. This module records the corresponding
equality of selected inertia subgroups explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- The selected prime has the same inertia subgroup under either
construction of the Galois action on the integral closure. -/
theorem normalizationAction_inertia_eq_integralClosure_inertia
    {C K N : Type u}
    [CommRing C] [Field K] [Field N]
    [Algebra C K] [IsFractionRing C K]
    [Algebra K N] [Algebra C N] [IsScalarTower C K N]
    [FiniteDimensional K N] [IsGalois K N]
    (P : Ideal (integralClosure C N)) :
    let T := integralClosure C N
    let G := N ≃ₐ[K] N
    letI : MulSemiringAction G T :=
      normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
    P.inertia G =
      (letI : MulSemiringAction G T :=
        IsIntegralClosure.MulSemiringAction C K N T
      P.inertia G) := by
  dsimp only
  rw [normalizationAction_eq_integralClosureAction (C := C) (K := K) (N := N)]

end

end HodgeConjecture.NormalizationInertia
