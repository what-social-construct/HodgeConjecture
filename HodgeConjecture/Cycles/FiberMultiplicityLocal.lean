module

public import HodgeConjecture.Cycles.FiniteFiberPullback
public import HodgeConjecture.Cycles.FiberStalkKernel

@[expose] public section

/-!
# Finite-fiber multiplicities as local quotient lengths

The actual scheme-fiber multiplicity is the length of the original source
stalk modulo the extension of the target maximal ideal. The comparison
uses the actual fiber inclusion and its stalk kernel; no compatibility
between independently supplied multiplicities is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

/-- A surjective stalk map identifies the source local ring with the actual quotient
of the target local ring, preserving the length of its regular module. -/
theorem stalkLength_eq_quotient_kernel {S X : Scheme.{u}} (i : S ⟶ X)
    [SurjectiveOnStalks i] (z : S) :
    Module.length (S.presheaf.stalk z) (S.presheaf.stalk z) =
      Module.length (X.presheaf.stalk (i.base z))
        ((X.presheaf.stalk (i.base z)) ⧸ RingHom.ker (i.stalkMap z).hom) := by
  let B := X.presheaf.stalk (i.base z)
  let I := RingHom.ker (i.stalkMap z).hom
  let e : (B ⧸ I) ≃+* S.presheaf.stalk z :=
    RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)
  rw [← length_regular_ringEquiv e]
  exact (Module.length_eq_of_surjective (S := B) Ideal.Quotient.mk_surjective).symm

/-- The local ring of the actual scheme fiber is the quotient by the extended maximal
ideal, with equality of lengths over their respective actual rings. -/
theorem fiber_stalkLength_eq_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (z : f.fiber y) :
    Module.length ((f.fiber y).presheaf.stalk z) ((f.fiber y).presheaf.stalk z) =
      Module.length (X.presheaf.stalk (f.fiberι y z))
        ((X.presheaf.stalk (f.fiberι y z)) ⧸
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (f.fiberι y z)))).map
            (f.stalkMap (f.fiberι y z)).hom) := by
  rw [stalkLength_eq_quotient_kernel (f.fiberι y) z, fiber_stalkMap_ker]

/-- The original multiplicity equals the local quotient-length expression used for
flat pullback of principal divisors. -/
theorem finiteFiberMultiplicity_eq_length_quotient {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    finiteFiberMultiplicity f x =
      (Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))).map
            (f.stalkMap x).hom)).toNat := by
  unfold finiteFiberMultiplicity
  rw [fiber_stalkLength_eq_quotient, f.fiberι_asFiber]

/-- Finiteness of the morphism makes the actual extended-maximal-ideal quotient have
finite length, so converting this length to a natural number loses no information. -/
theorem finiteFiber_quotient_length_ne_top {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) :
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))).map
          (f.stalkMap x).hom) ≠ ⊤ := by
  have h := finiteFiberMultiplicity_length_ne_top f x
  rwa [fiber_stalkLength_eq_quotient, f.fiberι_asFiber] at h

/-- Over the generic point of an integral target, the actual fiber multiplicity is the
length of the original source local ring. -/
theorem finiteFiberMultiplicity_over_genericPoint {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (x : X) (hx : f.base x = genericPoint Y) :
    finiteFiberMultiplicity f x =
      (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat := by
  rw [finiteFiberMultiplicity_eq_length_quotient]
  have hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x)) = ⊥ := by
    rw [hx]
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [hm, Ideal.map_bot, (AlgEquiv.quotientBot (X.presheaf.stalk x)
    (X.presheaf.stalk x)).toLinearEquiv.length_eq]

end

end HodgeConjecture.SchemeCycles
