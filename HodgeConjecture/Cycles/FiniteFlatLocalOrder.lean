module

public import HodgeConjecture.Cycles.FiberMultiplicityLocal
public import HodgeConjecture.Cycles.SchemeLocalOrder
public import HodgeConjecture.CommutativeAlgebra.FlatLocalMultiplicity

@[expose] public section

/-!
# The local coefficient calculation for finite flat principal pullback

The signed order in the original target local ring, multiplied by our
original actual fiber multiplicity, equals the sum of principal quotient
length differences over the minimal primes of the original source stalk.
In particular the multiplicity factor is not separately postulated.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

theorem finiteFlat_localOrder_fraction_eq_minimalPrime_sum
    {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X)
    (hy : ringKrullDim (Y.presheaf.stalk (f.base x)) = 1)
    (hx : ringKrullDim (X.presheaf.stalk x) = 1)
    (a b : Y.presheaf.stalk (f.base x)) (ha : a ≠ 0) (hb : b ≠ 0) :
    divisorOrder Y ⟨f.base x, hy⟩
        (Units.mk0 (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a)
            (by simpa only [map_zero] using
              (IsFractionRing.injective (Y.presheaf.stalk (f.base x)) Y.functionField).ne ha) /
          Units.mk0 (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b)
            (by simpa only [map_zero] using
              (IsFractionRing.injective (Y.presheaf.stalk (f.base x)) Y.functionField).ne hb)) *
        (finiteFiberMultiplicity f x : ℤ) =
      ∑ᶠ p : {p : PrimeSpectrum (X.presheaf.stalk x) //
          p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
        (((Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ (Ideal.span {(f.stalkMap x).hom a} ⊔ p.1.asIdeal))).toNat : ℤ) -
         ((Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ (Ideal.span {(f.stalkMap x).hom b} ⊔ p.1.asIdeal))).toNat : ℤ)) := by
  let A := Y.presheaf.stalk (f.base x)
  let B := X.presheaf.stalk x
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (le_of_eq hy)
  letI : Algebra A B := (f.stalkMap x).hom.toAlgebra
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp (Flat.stalkMap f x)
  letI : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  change localOrder A _ * _ = _
  rw [localOrder_fraction A a b ha hb, finiteFiberMultiplicity_eq_length_quotient]
  exact flatLocal_length_difference_eq_sum_minimalPrimes hx a b ha hb

end

end HodgeConjecture.SchemeCycles
