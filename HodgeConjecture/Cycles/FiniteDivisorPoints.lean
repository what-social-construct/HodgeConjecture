module

public import HodgeConjecture.Cycles.FiniteGrading
public import HodgeConjecture.Cycles.IntegralCodimension

@[expose] public section

/-!
# Divisor points under finite dominant maps over a field

These are consequences of the existing codimension/dimension formula and
finite-map grading theorem. No new codimension or grading is defined.
The finite dominant, integral, locally finite-type field setting supplies
the codimension-one correspondence used for the finite case of Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
  (f : X ⟶ Y) [IsFinite f] [IsDominant f]

include pY

/-- The existing point codimensions agree under a finite dominant map in the field setting. -/
theorem point_coheight_eq_of_finite_dominant (x : X) :
    Order.coheight x = Order.coheight (f.base x) := by
  have hX := point_coheight_add_dimension_of_integral_locallyOfFiniteType k X (f ≫ pY) x
  have hY := point_coheight_add_dimension_of_integral_locallyOfFiniteType k Y pY (f.base x)
  rw [DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k pY f x,
    DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k pY f (genericPoint X),
    genericPoint_eq_of_isDominant f] at hX
  have hn : (Order.coheight x).toNat = (Order.coheight (f.base x)).toNat := by omega
  rw [← ENat.coe_toNat (point_coheight_ne_top_of_integral_locallyOfFiniteType k X (f ≫ pY) x),
    ← ENat.coe_toNat (point_coheight_ne_top_of_integral_locallyOfFiniteType k Y pY (f.base x)), hn]

/-- Actual stalk dimensions agree, by the already proved codimension/stalk comparison. -/
theorem stalkDimension_finite_dominant (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f.base x)) := by
  rw [← point_coheight_eq_stalkDim X x, ← point_coheight_eq_stalkDim Y (f.base x),
    point_coheight_eq_of_finite_dominant k pY f x]

/-- The actual finite image preserves support codimension in this geometric setting. -/
theorem supportCodimension_finite_dominant (W : IntegralClosedSubscheme X) :
    supportCodimension (imageSubscheme f W) = supportCodimension W := by
  apply WithBot.coe_injective
  rw [supportCodimension_eq_stalkDim, supportCodimension_eq_stalkDim,
    ambientGenericPoint_imageSubscheme, stalkDimension_finite_dominant k pY f]

/-- A point in the actual fiber of a divisor point is an existing source divisor point. -/
def divisorPointOfFiniteFiber (y : DivisorPoint Y) (x : {x : X // f.base x = y.val}) :
    DivisorPoint X :=
  ⟨x.val, by rw [stalkDimension_finite_dominant k pY f, x.property]; exact y.property⟩

@[simp]
theorem divisorPointOfFiniteFiber_val (y : DivisorPoint Y)
    (x : {x : X // f.base x = y.val}) :
    (divisorPointOfFiniteFiber k pY f y x).val = x.val := rfl

end

end HodgeConjecture.SchemeCycles
