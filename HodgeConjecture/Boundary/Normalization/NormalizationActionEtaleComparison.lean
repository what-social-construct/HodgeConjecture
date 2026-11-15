module

public import HodgeConjecture.Boundary.Normalization.NormalizationActionFixedPointsComparison
public import HodgeConjecture.Boundary.Normalization.FixedPointsBaseComparison
public import HodgeConjecture.Boundary.Normalization.NormalizationFixedRingLocalization

@[expose] public section

/-!
# Selected fixed-ring étaleness under the normalization actions

The DVR theorem uses Mathlib's action on the integral closure, while the
normalization descent uses the project's transported Galois action. Equality
of the actions identifies their selected inertia fixed rings and therefore
their étale localizations.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- Étaleness of the selected inertia-fixed localization under Mathlib's
integral-closure action also holds under the project's normalization action. -/
theorem normalizationAction_etale_atPrime_of_integralClosureAction
    {C K N : Type u}
    [CommRing C] [Field K] [Field N]
    [Algebra C K] [IsFractionRing C K]
    [Algebra K N] [Algebra C N] [IsScalarTower C K N]
    [FiniteDimensional K N] [IsGalois K N]
    (P : Ideal (integralClosure C N)) [P.IsPrime]
    (h :
      let T := integralClosure C N
      let G := N ≃ₐ[K] N
      letI : MulSemiringAction G T :=
        IsIntegralClosure.MulSemiringAction C K N T
      letI : SMulCommClass G C T :=
        integralClosureActionSMulCommClass (C := C) (K := K) (N := N)
      let I := P.inertia G
      let F := FixedPoints.subalgebra C T I
      Algebra.Etale C (Localization.AtPrime (P.under F))) :
    let T := integralClosure C N
    let G := N ≃ₐ[K] N
    letI : MulSemiringAction G T :=
      normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
    let I := P.inertia G
    let F := FixedPoints.subalgebra C T I
    Algebra.Etale C (Localization.AtPrime (P.under F)) := by
  let T := integralClosure C N
  let G := N ≃ₐ[K] N
  letI : MulSemiringAction G T :=
    normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
  let I := P.inertia G
  let F := FixedPoints.subalgebra C T I
  have hI : I =
      (letI : MulSemiringAction G T :=
        IsIntegralClosure.MulSemiringAction C K N T
      P.inertia G) :=
    normalizationAction_inertia_eq_integralClosure_inertia P
  have hF : F =
      (letI : MulSemiringAction G T :=
        IsIntegralClosure.MulSemiringAction C K N T
      letI : SMulCommClass G C T :=
        integralClosureActionSMulCommClass (C := C) (K := K) (N := N)
      FixedPoints.subalgebra C T (P.inertia G)) := by
    calc
      F =
          (letI : MulSemiringAction G T :=
            IsIntegralClosure.MulSemiringAction C K N T
          letI : SMulCommClass G C T :=
            integralClosureActionSMulCommClass (C := C) (K := K) (N := N)
          FixedPoints.subalgebra C T I) :=
        normalizationAction_fixedSubalgebra_eq_integralClosure_fixedSubalgebra I
      _ = _ := by rw [hI]
  change Algebra.Etale C (Localization.AtPrime (P.under F))
  rw [hF]
  exact h

/-- The DVR étaleness result under Mathlib's action applies to the project's
inertia-fixed local ring, presented as a fixed `B`-subalgebra. -/
theorem normalizationAction_etale_atPrime_of_integralClosureAction_baseChange
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [Algebra C K] [IsFractionRing C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N]
    [FiniteDimensional K N] [IsGalois K N]
    (P : Ideal (integralClosure C N)) [P.IsPrime]
    (h :
      let T := integralClosure C N
      let G := N ≃ₐ[K] N
      letI : MulSemiringAction G T :=
        IsIntegralClosure.MulSemiringAction C K N T
      letI : SMulCommClass G C T :=
        integralClosureActionSMulCommClass (C := C) (K := K) (N := N)
      let I := P.inertia G
      let F := FixedPoints.subalgebra C T I
      Algebra.Etale C (Localization.AtPrime (P.under F))) :
    let T := integralClosure C N
    let G := N ≃ₐ[K] N
    letI : MulSemiringAction G T :=
      normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
    letI : SMulCommClass G B T :=
      normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
    let I := P.inertia G
    let F := FixedPoints.subalgebra B T I
    letI : Algebra C (Localization.AtPrime (P.under F)) :=
      fixedPointsBaseChangeAtPrimeAlgebra I P
    Algebra.Etale C (Localization.AtPrime (P.under F)) := by
  let T := integralClosure C N
  let G := N ≃ₐ[K] N
  letI : MulSemiringAction G T :=
    normalClosureNormalizationRingMulSemiringAction (B := C) (K := K) (N := N)
  letI : SMulCommClass G B T :=
    normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
  let I := P.inertia G
  have hC : Algebra.Etale C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra C T I))) :=
    normalizationAction_etale_atPrime_of_integralClosureAction P h
  exact fixedPointsBaseChange_etale_atPrime (B := B) (C := C)
    (T := T) I P hC

end

end HodgeConjecture.NormalizationInertia
