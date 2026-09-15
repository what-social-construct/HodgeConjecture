import HodgeConjecture.Cycles.LocalOrder
import HodgeConjecture.Cycles.LocalOrderTransport
import HodgeConjecture.Cycles.FunctionFieldTransport
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.Height

/-!
# Local divisor coefficients and their geometric transport

A divisor point is an actual scheme point whose local ring has dimension
one. On an integral locally Noetherian scheme its signed order is defined
using that local ring and the actual scheme function field. Scheme
isomorphisms preserve the points, function fields, and signed coefficients.

Height-one primes in an affine chart give these points. `DivisorSupport`
identifies them with actual codimension-one integral closed supports.
Finite support, graded principal-divisor cycles, and rational-equivalence
relations are subsequent steps, not part of this pointwise construction.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Actual scheme points with one-dimensional local ring. -/
def DivisorPoint (X : Scheme.{u}) :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

instance divisorPoint_stalkKrullDimLE (X : Scheme.{u}) (x : DivisorPoint X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x.val) :=
  Ring.krullDimLE_iff.mpr (le_of_eq x.property)

/-- Local dimensions are preserved by the actual stalk map of an isomorphism. -/
theorem stalkDimension_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    ringKrullDim (Y.presheaf.stalk (e.hom.base x)) =
      ringKrullDim (X.presheaf.stalk x) :=
  (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv.ringKrullDim

/-- The actual point equivalence restricts to the one-dimensional local rings. -/
def divisorPointEquiv {X Y : Scheme.{u}} (e : X ≅ Y) :
    DivisorPoint X ≃ DivisorPoint Y :=
  (Scheme.homeoOfIso e).toEquiv.subtypeEquiv fun x ↦ by
    change ringKrullDim (X.presheaf.stalk x) = 1 ↔
      ringKrullDim (Y.presheaf.stalk (e.hom.base x)) = 1
    rw [stalkDimension_iso]

@[simp]
theorem divisorPointEquiv_val {X Y : Scheme.{u}} (e : X ≅ Y) (x : DivisorPoint X) :
    (divisorPointEquiv e x).val = e.hom.base x.val := rfl

/-- A height-one prime in any actual affine chart supplies a divisor point. -/
def divisorPointOfAffineHeightOne (X : Scheme.{u}) {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (h : (hU.primeIdealOf x).asIdeal.height = 1) :
    DivisorPoint X := by
  refine ⟨x.val, ?_⟩
  letI := hU.isLocalization_stalk x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf x).asIdeal,
    h]
  rfl

/-- The signed local coefficient of an actual nonzero rational function. -/
def divisorOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) (f : X.functionFieldˣ) : ℤ :=
  localOrder (X.presheaf.stalk x.val) f

@[simp]
theorem divisorOrder_one (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) : divisorOrder X x 1 = 0 :=
  localOrder_one _

theorem divisorOrder_mul (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) (f g : X.functionFieldˣ) :
    divisorOrder X x (f * g) = divisorOrder X x f + divisorOrder X x g :=
  localOrder_mul _ f g

@[simp]
theorem divisorOrder_inv (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) (f : X.functionFieldˣ) :
    divisorOrder X x f⁻¹ = -divisorOrder X x f :=
  localOrder_inv _ f

/-- The coefficient on a nonzero local element is its actual quotient length. -/
theorem divisorOrder_algebraMap (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) (a : X.presheaf.stalk x.val) (ha : a ≠ 0) :
    divisorOrder X x (Units.mk0 (algebraMap (X.presheaf.stalk x.val) X.functionField a)
      (by simpa only [map_zero] using
        (IsFractionRing.injective (X.presheaf.stalk x.val) X.functionField).ne ha)) =
      ((Module.length (X.presheaf.stalk x.val)
        ((X.presheaf.stalk x.val) ⧸ Ideal.span {a})).toNat : ℤ) :=
  localOrder_algebraMap _ a ha

/-- Actual scheme isomorphisms preserve local divisor coefficients through
their proved contravariant function-field and stalk maps. -/
theorem divisorOrder_iso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (x : DivisorPoint X) (f : Y.functionFieldˣ) :
    divisorOrder X x (Units.map (functionFieldEquiv e).toMonoidHom f) =
      divisorOrder Y (divisorPointEquiv e x) f := by
  letI : Ring.KrullDimLE 1 (Y.presheaf.stalk (e.hom.base x.val)) :=
    divisorPoint_stalkKrullDimLE Y (divisorPointEquiv e x)
  change WithZero.log (Ring.ordFrac (X.presheaf.stalk x.val)
      (functionFieldEquiv e (f : Y.functionField))) =
    WithZero.log (Ring.ordFrac (Y.presheaf.stalk (e.hom.base x.val)) (f : Y.functionField))
  exact congrArg WithZero.log (ordFrac_ringEquiv
    (asIso (e.hom.stalkMap x.val)).commRingCatIsoToRingEquiv
    (functionFieldEquiv e) (functionFieldEquiv_algebraMap e x.val) (f : Y.functionField))

end

end HodgeConjecture.SchemeCycles
