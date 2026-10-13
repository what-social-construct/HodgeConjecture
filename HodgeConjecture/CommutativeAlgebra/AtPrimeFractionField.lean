import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Ideal.Height

/-!
# A prime localization in the original fraction field

The canonical map `B_q → L` extends `B → L`. Its scalar tower and fraction
field property are proved from localization. The instances are scoped to
`AtPrimeFractionField`, so importing this file does not select an algebra
structure for callers. This supplies the local orders in Stacks Tag 02MJ:
https://stacks.math.columbia.edu/tag/02MJ
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

namespace AtPrimeFractionField

variable (B L : Type*) [CommRing B] [IsDomain B] [Field L]
  [Algebra B L] [IsFractionRing B L] (q : Ideal B) [q.IsPrime]

/-- The canonical algebra on the original fraction field from a prime localization. -/
scoped instance algebra : Algebra (Localization.AtPrime q) L :=
  (Localization.mapToFractionRing L q.primeCompl (Localization.AtPrime q)
    q.primeCompl_le_nonZeroDivisors).toRingHom.toAlgebra

/-- The canonical localization map extends the given map from the domain. -/
scoped instance scalarTower : IsScalarTower B (Localization.AtPrime q) L :=
  IsScalarTower.of_algHom (Localization.mapToFractionRing L q.primeCompl
    (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors)

/-- The original field is also the fraction field of the prime localization. -/
scoped instance isFractionRing : IsFractionRing (Localization.AtPrime q) L :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl
    (Localization.AtPrime q) L

end AtPrimeFractionField

/-- The dimension bound needed for local orders descends to prime localizations. -/
theorem atPrime_krullDimLE_one (B : Type*) [CommRing B] [Ring.KrullDimLE 1 B]
    (q : Ideal B) [q.IsPrime] : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
  apply Ring.krullDimLE_iff.mpr
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)).trans
    (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 B›)

end

end HodgeConjecture.CommutativeAlgebra
