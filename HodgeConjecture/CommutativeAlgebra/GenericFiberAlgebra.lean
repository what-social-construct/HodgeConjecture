import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.FiniteType

/-!
# The actual generic-fiber algebra

For an `R`-algebra `S`, the carrier is any actual localization of `S` at
the image of the non-zero-divisors of `R`. The fraction-ring algebra is
the existing localization map; no new carrier or global algebra instance
is introduced. Its actual localization pushout proves finite type over
the fraction ring. Domain and injectivity properties use the actual
denominator images.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v w t

variable (R : Type u) (S : Type v) (S' : Type w)
  [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S']
  [IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S']

/-- The canonical fraction-ring algebra is the actual localization map.
Install it locally when the actual carrier has no algebra instance yet. -/
def genericFiberAlgebra : Algebra (FractionRing R) S' :=
  localizationAlgebra (nonZeroDivisors R) S

/-- The canonical generic-fiber algebra retains the actual localization map. -/
theorem genericFiberAlgebra_algebraMap_eq :
    letI := genericFiberAlgebra R S S'
    algebraMap (FractionRing R) S' =
      (IsLocalization.map (M := nonZeroDivisors R) (S := FractionRing R)
        (T := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S' (algebraMap R S)
        (Submonoid.le_comap_map (nonZeroDivisors R)) : FractionRing R →+* S') := rfl

/-- The two actual routes from the base ring to its generic fiber commute. -/
theorem genericFiberAlgebra_isScalarTower
    [Algebra R S'] [IsScalarTower R S S'] :
    letI := genericFiberAlgebra R S S'
    IsScalarTower R (FractionRing R) S' := by
  letI := genericFiberAlgebra R S S'
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [genericFiberAlgebra_algebraMap_eq R S S']
  rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply R S S']

/-- Any compatible fraction-ring algebra on the actual localization is
finite type when the original algebra is finite type. The proof uses
the actual localization pushout, not a replacement of the carrier. -/
theorem genericFiber_finiteType
    [Algebra R S'] [Algebra (FractionRing R) S']
    [IsScalarTower R S S'] [IsScalarTower R (FractionRing R) S']
    [Algebra.FiniteType R S] : Algebra.FiniteType (FractionRing R) S' := by
  letI : Algebra.IsPushout R S (FractionRing R) S' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors R) (FractionRing R) S S'
  letI : Algebra.IsPushout R (FractionRing R) S S' :=
    (inferInstance : Algebra.IsPushout R S (FractionRing R) S').symm
  exact Algebra.FiniteType.equiv inferInstance
    (Algebra.IsPushout.equiv R (FractionRing R) S S')

/-- An injective map into a domain sends every base denominator to a
non-zero-divisor of the upper ring. -/
theorem genericFiber_denominators_le_nonZeroDivisors
    [IsDomain S] (hinj : Function.Injective (algebraMap R S)) :
    Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S :=
  Submonoid.map_le_of_le_comap _
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)

/-- The actual localization is a domain when the upper ring is a domain
and the original algebra map is injective. -/
theorem genericFiber_isDomain [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) : IsDomain S' :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S'
    (genericFiber_denominators_le_nonZeroDivisors R S hinj)

/-- The map from the original upper ring into its actual generic fiber
is injective under the denominator condition proved above. -/
theorem genericFiber_localization_injective [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap S S') :=
  IsLocalization.injective S'
    (genericFiber_denominators_le_nonZeroDivisors R S hinj)

/-- Over a domain base, its actual fraction field embeds into the
nontrivial generic fiber. -/
theorem genericFiber_baseField_injective [IsDomain R] [IsDomain S]
    [Algebra (FractionRing R) S']
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap (FractionRing R) S') := by
  letI : IsDomain S' := genericFiber_isDomain R S S' hinj
  exact (algebraMap (FractionRing R) S').injective

/-- A compatible smaller-base scalar tower remains compatible with
the fraction-ring route to the actual generic fiber. -/
theorem genericFiber_isScalarTower_base
    (k : Type t) (K : Type*) [CommRing k] [CommRing K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra k R] [Algebra k K] [Algebra k S'] [Algebra R S'] [Algebra K S']
    [IsScalarTower k R K] [IsScalarTower k R S'] [IsScalarTower R K S'] :
    IsScalarTower k K S' := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [IsScalarTower.algebraMap_apply k R S',
    IsScalarTower.algebraMap_apply k R K,
    ← IsScalarTower.algebraMap_apply R K S']

end

end HodgeConjecture.CommutativeAlgebra
