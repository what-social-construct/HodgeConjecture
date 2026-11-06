module

public import HodgeConjecture.Cycles.DivisorSupport
public import Mathlib.Order.Cover

@[expose] public section

/-!
# Explicit dimension functions and degrees of actual supports

A dimension function is an integer-valued function that is strictly
increasing in the scheme's point order and increases by one across a
cover. This order is inclusion of point closures: a generization is above
its specialization. Both conditions of Stacks, Definition 5.20.1 (02I9),
are retained, without assuming local Noetherianity or existence of such a
function on every scheme.

The degree of an existing integral closed support is the value at its
actual ambient generic point. On an integral scheme a prime divisor's
generic point is immediately below the ambient generic point, so its
degree is one less. This uses the proved chain codimension, not a
subtraction of absolute Krull dimensions.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- A dimension function with both strict specialization monotonicity and
the unit step for immediate specializations explicitly supplied. -/
structure DimensionFunction (X : Scheme.{u}) where
  toFun : X → ℤ
  strictMono : StrictMono toFun
  map_covBy : ∀ {x y : X}, x ⋖ y → toFun y = toFun x + 1

instance {X : Scheme.{u}} : CoeFun (DimensionFunction X) (fun _ ↦ X → ℤ) :=
  ⟨DimensionFunction.toFun⟩

/-- The degree of an actual integral support is the dimension function at
its ambient generic point. -/
def supportDegree {X : Scheme.{u}} (δ : DimensionFunction X)
    (Z : IntegralClosedSubscheme X) : ℤ :=
  δ (ambientGenericPoint Z)

/-- A prime divisor's ambient generic point is an immediate specialization
of the generic point of an integral scheme. No Noetherianity is needed. -/
theorem primeDivisor_covBy_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (Z : PrimeDivisor X) : ambientGenericPoint Z.val ⋖ genericPoint X := by
  have hle (x : X) : x ≤ genericPoint X :=
    Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
  have hmax : IsMax (genericPoint X) := fun x _ ↦ hle x
  have htop : Order.coheight (genericPoint X) = 0 :=
    Order.coheight_eq_zero.mpr hmax
  have hZ : Order.coheight (ambientGenericPoint Z.val) = 1 := by
    have h := Z.property
    change Order.coheight (integralSupport Z.val) = 1 at h
    rwa [integralSupport_eq_pointClosure, pointClosure_coheight] at h
  refine ⟨lt_of_le_not_ge (hle _) ?_, ?_⟩
  · intro hge
    have h : genericPoint X = ambientGenericPoint Z.val :=
      ((Scheme.le_iff_specializes.mp (hle _)).antisymm
        (Scheme.le_iff_specializes.mp hge)).eq
    rw [← h, htop] at hZ
    exact zero_ne_one hZ
  · intro y hZy hy
    have hbound : Order.coheight y ≤ 0 :=
      ((Order.coheight_eq_coe_add_one_iff (n := 0)).mp (by simpa using hZ)).2.2 y hZy
    have hpos := Order.coheight_add_one_le hy
    rw [htop, zero_add] at hpos
    exact (not_le_of_gt (zero_lt_one : (0 : ℕ∞) < 1)) (hpos.trans hbound)

/-- The chosen dimension function places prime supports one degree below
the generic point of an integral ambient scheme. -/
theorem supportDegree_primeDivisor {X : Scheme.{u}} [IsIntegral X]
    (δ : DimensionFunction X) (Z : PrimeDivisor X) :
    supportDegree δ Z.val = δ (genericPoint X) - 1 := by
  have h := δ.map_covBy (primeDivisor_covBy_genericPoint X Z)
  change δ (ambientGenericPoint Z.val) = δ (genericPoint X) - 1
  rw [h, add_sub_cancel_right]

/-- The support degree of an actual closed image is the target dimension
function evaluated at the actual image of the source generic point.
Only the support composite is required to be a closed immersion. -/
theorem supportDegree_closedImageSubscheme {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (f : X ⟶ Y) (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    supportDegree δ (closedImageSubscheme f Z) =
      δ (f.base (ambientGenericPoint Z)) := by
  rw [supportDegree, ambientGenericPoint_closedImageSubscheme]

end

end HodgeConjecture.SchemeCycles
