module

public import HodgeConjecture.Boundary.Normalization.NormalizationActionInertiaComparison

@[expose] public section

/-!
# Fixed subalgebras under the two normalization actions

The action comparison also identifies the subalgebras fixed by a selected
subgroup, including the inertia subgroup at a selected prime.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- Mathlib's integral-closure Galois action fixes the localized base. -/
theorem integralClosureActionSMulCommClass
    {C K N : Type u}
    [CommRing C] [Field K] [Field N]
    [Algebra C K] [IsFractionRing C K]
    [Algebra K N] [Algebra C N] [IsScalarTower C K N]
    [FiniteDimensional K N] [IsGalois K N] :
    let T := integralClosure C N
    let G := N ≃ₐ[K] N
    letI : MulSemiringAction G T :=
      IsIntegralClosure.MulSemiringAction C K N T
    SMulCommClass G C T := by
  dsimp only
  rw [← normalizationAction_eq_integralClosureAction (C := C) (K := K) (N := N)]
  infer_instance

/-- A subgroup fixes the same subalgebra under the project action and
Mathlib's integral-closure Galois action. -/
theorem normalizationAction_fixedSubalgebra_eq_integralClosure_fixedSubalgebra
    {C K N : Type u}
    [CommRing C] [Field K] [Field N]
    [Algebra C K] [IsFractionRing C K]
    [Algebra K N] [Algebra C N] [IsScalarTower C K N]
    [FiniteDimensional K N] [IsGalois K N]
    (H : Subgroup (N ≃ₐ[K] N)) :
    let T := integralClosure C N
    let G := N ≃ₐ[K] N
    (letI : MulSemiringAction G T :=
       normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
     FixedPoints.subalgebra C T H) =
      (letI : MulSemiringAction G T :=
         IsIntegralClosure.MulSemiringAction C K N T
       letI : SMulCommClass G C T :=
         integralClosureActionSMulCommClass (C := C) (K := K) (N := N)
       FixedPoints.subalgebra C T H) := by
  dsimp only
  let T := integralClosure C N
  let G := N ≃ₐ[K] N
  have hsmul (g : G) (x : T) :
      (letI : MulSemiringAction G T :=
        normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
      g • x) =
        (letI : MulSemiringAction G T :=
          IsIntegralClosure.MulSemiringAction C K N T
        g • x) := by
    rw [normalizationAction_eq_integralClosureAction (C := C) (K := K) (N := N)]
  apply Subalgebra.ext
  intro x
  constructor
  · intro hx g
    change (letI : MulSemiringAction G T :=
      IsIntegralClosure.MulSemiringAction C K N T
      (g : G) • x) = x
    rw [← hsmul (g : G) x]
    exact hx g
  · intro hx g
    change (letI : MulSemiringAction G T :=
      normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
      (g : G) • x) = x
    rw [hsmul (g : G) x]
    exact hx g

end

end HodgeConjecture.NormalizationInertia
