module

public import HodgeConjecture.Boundary.Normalization.InvariantIntermediate
public import HodgeConjecture.Boundary.Normalization.DvrInertiaFixedRing

@[expose] public section

/-!
# The two normalization Galois actions

The normalization diagrams use the action transported by
`AlgEquiv.mapIntegralClosure`, while the DVR inertia theorem uses Mathlib's
`IsIntegralClosure.MulSemiringAction`. Both send an integral element to the
same Galois conjugate in the ambient field.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- The project action and Mathlib's integral-closure action agree on every
element of the localized normalization. -/
theorem normalizationAction_eq_integralClosureAction
    {C K N : Type u}
    [CommRing C] [Field K] [Field N]
    [Algebra C K] [IsFractionRing C K]
    [Algebra K N] [Algebra C N] [IsScalarTower C K N]
    [FiniteDimensional K N] [IsGalois K N] :
    (normalClosureNormalizationRingMulSemiringAction
      (B := C) (K := K) (N := N)) =
      IsIntegralClosure.MulSemiringAction C K N (integralClosure C N) := by
  let T := integralClosure C N
  have hhom :
      normalClosureNormalizationRingActionHom (B := C) (K := K) (N := N) =
        (galRestrict C K N T).toMonoidHom := by
    ext σ x
    change σ (x : N) = ((galRestrict C K N T σ x : T) : N)
    exact (algebraMap_galRestrict_apply C σ x).symm
  change MulSemiringAction.compHom T
      (normalClosureNormalizationRingActionHom (B := C) (K := K) (N := N)) =
    MulSemiringAction.compHom T (galRestrict C K N T).toMonoidHom
  rw [hhom]

end

end HodgeConjecture.NormalizationInertia
