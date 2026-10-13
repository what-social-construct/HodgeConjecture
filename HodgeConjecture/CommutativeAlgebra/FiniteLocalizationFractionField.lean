import HodgeConjecture.CommutativeAlgebra.FiniteLocalization
import Mathlib.RingTheory.Localization.AsSubring

/-!
# The fraction field of the whole localized finite algebra

The canonical localization maps retain the original fraction fields and
their scalar actions. These are the rings and maps used when applying the
local norm formula over an actual target stalk in Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A) [p.IsPrime]

/-- The denominator set avoids zero in an injective extension of domains. -/
theorem finiteLocalization_denominators [IsDomain A] [IsDomain B] [FaithfulSMul A B] :
    Algebra.algebraMapSubmonoid B p.primeCompl ≤ nonZeroDivisors B := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr
    (nonZeroDivisors.ne_zero (p.primeCompl_le_nonZeroDivisors ha))

/-- The whole localization remains a domain. -/
theorem finiteLocalization_isDomain [IsDomain A] [IsDomain B] [FaithfulSMul A B] :
    IsDomain (finiteLocalization A B p) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (finiteLocalization_denominators A B p)

namespace FiniteLocalizationFractionField

variable (L : Type*) [IsDomain A] [IsDomain B] [FaithfulSMul A B]
  [Field L] [Algebra B L] [IsFractionRing B L]

/-- The original fraction field receives the canonical map from the whole localization. -/
scoped instance algebra : Algebra (finiteLocalization A B p) L :=
  (Localization.mapToFractionRing L (Algebra.algebraMapSubmonoid B p.primeCompl)
    (finiteLocalization A B p) (finiteLocalization_denominators A B p)).toRingHom.toAlgebra

/-- The canonical map agrees with the original map on the finite algebra. -/
scoped instance scalarTower : IsScalarTower B (finiteLocalization A B p) L :=
  IsScalarTower.of_algHom (Localization.mapToFractionRing L
    (Algebra.algebraMapSubmonoid B p.primeCompl) (finiteLocalization A B p)
    (finiteLocalization_denominators A B p))

/-- Localizing the finite algebra leaves its original fraction field unchanged. -/
scoped instance isFractionRing : IsFractionRing (finiteLocalization A B p) L :=
  IsFractionRing.isFractionRing_of_isLocalization
    (Algebra.algebraMapSubmonoid B p.primeCompl) (finiteLocalization A B p) L
    (finiteLocalization_denominators A B p)

end FiniteLocalizationFractionField

variable (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p]

/-- The whole localization is an algebra over any actual localization of the base at `p`. -/
abbrev finiteLocalization_baseAlgebra : Algebra R (finiteLocalization A B p) :=
  localizationAlgebra p.primeCompl B

/-- The canonical localized algebra map respects the original section map. -/
theorem finiteLocalization_baseScalarTower :
    letI := finiteLocalization_baseAlgebra A B p R
    IsScalarTower A R (finiteLocalization A B p) := by
  letI := finiteLocalization_baseAlgebra A B p R
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (IsLocalization.map_eq (S := R) (Q := finiteLocalization A B p)
    (T := Algebra.algebraMapSubmonoid B p.primeCompl)
    p.primeCompl.le_comap_map a).symm

end

end HodgeConjecture.CommutativeAlgebra
