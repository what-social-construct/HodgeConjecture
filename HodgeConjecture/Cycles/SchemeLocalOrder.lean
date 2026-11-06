module

public import HodgeConjecture.Cycles.LocalOrder
public import HodgeConjecture.Cycles.LocalOrderTransport
public import HodgeConjecture.Cycles.FunctionFieldTransport
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

/-!
# Local divisor coefficients and their geometric transport

A divisor point is an actual scheme point whose local ring has dimension
one. On an integral locally Noetherian scheme its signed order is defined
using that local ring and the actual scheme function field. Open immersions
embed the divisor points and preserve their signed coefficients through
the actual contravariant function-field equivalence. The existing
isomorphism comparisons specialize these same maps.

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

/-- An actual open immersion preserves local dimension through its stalk isomorphism. -/
theorem stalkDimension_openImmersion {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    ringKrullDim (Y.presheaf.stalk (j.base x)) =
      ringKrullDim (X.presheaf.stalk x) :=
  (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.ringKrullDim

/-- The actual open point map embeds the points with one-dimensional local ring. -/
def divisorPointEmbedding {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    DivisorPoint X ↪ DivisorPoint Y where
  toFun x := ⟨j.base x.val, (stalkDimension_openImmersion j x.val).trans x.property⟩
  inj' := by
    intro x y h
    exact Subtype.ext (j.isOpenEmbedding.injective (congrArg Subtype.val h))

@[simp]
theorem divisorPointEmbedding_val {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (x : DivisorPoint X) :
    (divisorPointEmbedding j x).val = j.base x.val := rfl

/-- The divisor points in the image are exactly those lying in the actual open image. -/
theorem mem_range_divisorPointEmbedding_iff {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (y : DivisorPoint Y) :
    y ∈ Set.range (divisorPointEmbedding j) ↔ y.val ∈ Set.range j.base := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, rfl⟩
  · rintro ⟨x, hx⟩
    have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
      rw [← stalkDimension_openImmersion j x, hx]
      exact y.property
    exact ⟨⟨x, hdim⟩, Subtype.ext hx⟩

/-- The existing isomorphism comparison is the open-immersion specialization. -/
theorem stalkDimension_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    ringKrullDim (Y.presheaf.stalk (e.hom.base x)) =
      ringKrullDim (X.presheaf.stalk x) :=
  stalkDimension_openImmersion e.hom x

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

@[simp]
theorem divisorPointEmbedding_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : DivisorPoint X) :
    divisorPointEmbedding e.hom x = divisorPointEquiv e x := rfl

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

/-- Actual integral open immersions preserve signed local orders. Local
Noetherianity on the source is derived from the target, not an extra premise. -/
theorem divisorOrder_openImmersion {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j] (x : DivisorPoint X) (f : Y.functionFieldˣ) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
    divisorOrder X x (Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom f) =
      divisorOrder Y (divisorPointEmbedding j x) f := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  letI : Ring.KrullDimLE 1 (Y.presheaf.stalk (j.base x.val)) :=
    divisorPoint_stalkKrullDimLE Y (divisorPointEmbedding j x)
  change WithZero.log (Ring.ordFrac (X.presheaf.stalk x.val)
      (functionFieldEquivOfOpenImmersion j (f : Y.functionField))) =
    WithZero.log (Ring.ordFrac (Y.presheaf.stalk (j.base x.val)) (f : Y.functionField))
  exact congrArg WithZero.log (ordFrac_ringEquiv
    (asIso (j.stalkMap x.val)).commRingCatIsoToRingEquiv
    (functionFieldEquivOfOpenImmersion j)
    (functionFieldEquivOfOpenImmersion_algebraMap j x.val) (f : Y.functionField))

/-- The existing isomorphism order comparison specializes the actual open comparison. -/
theorem divisorOrder_iso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (x : DivisorPoint X) (f : Y.functionFieldˣ) :
    divisorOrder X x (Units.map (functionFieldEquiv e).toMonoidHom f) =
      divisorOrder Y (divisorPointEquiv e x) f :=
  divisorOrder_openImmersion e.hom x f

end

end HodgeConjecture.SchemeCycles
