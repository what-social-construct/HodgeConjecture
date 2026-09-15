import HodgeConjecture.Cycles.PointSupport
import HodgeConjecture.Cycles.SupportCodimension

/-!
# The actual dimension of integral closed carriers

The points of an integral closed carrier are exactly the specializations
of its ambient generic point, with their actual specialization order.
Consequently its topological Krull dimension is the height of that point.
This is dimension of the carrier, not codimension in its ambient scheme.

On a finite-dimensional ambient scheme the height is a genuine finite
integer and strictly increases along proper generization. No unit-step
law for immediate specialization is inferred from finiteness alone.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The actual closed carrier, as the interval of specializations of its
ambient generic point. -/
def integralSubschemePointOrderIso {X : Scheme.{u}} (W : IntegralClosedSubscheme X) :
    W.val.subscheme ≃o Set.Iic (ambientGenericPoint W) where
  toEquiv := Equiv.setCongr (by
    ext x
    exact (ambientGenericPoint_isGenericPoint W).specializes_iff_mem.symm)
  map_rel_iff' := by
    intro x y
    change W.val.subschemeι.base y ⤳ W.val.subschemeι.base x ↔ y ⤳ x
    exact W.val.subschemeι.isClosedEmbedding.isInducing.specializes_iff

/-- This order comparison retains the literal closed-inclusion point map. -/
@[simp]
theorem integralSubschemePointOrderIso_val {X : Scheme.{u}}
    (W : IntegralClosedSubscheme X) (x : W.val.subscheme) :
    (integralSubschemePointOrderIso W x).val = W.val.subschemeι.base x := rfl

/-- Sobriety identifies the Krull dimension of scheme points with the
Krull dimension of its irreducible closed subsets. -/
theorem topologicalKrullDim_eq_pointKrullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  (Order.krullDim_eq_of_orderIso (pointClosureOrderIso X)).symm

/-- The generic point of an integral scheme has height equal to the
dimension of that scheme. -/
theorem genericPoint_height_eq_topologicalKrullDim (X : Scheme.{u}) [IsIntegral X] :
    (Order.height (genericPoint X) : WithBot ℕ∞) = topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_pointKrullDim]
  apply le_antisymm (Order.height_le_krullDim _)
  rw [Order.krullDim_eq_iSup_height_of_nonempty]
  apply WithBot.coe_le_coe.mpr
  exact iSup_le fun x ↦ Order.height_mono
    (Scheme.le_iff_specializes.mpr (genericPoint_specializes x))

/-- The carrier's actual topological dimension is the height of its
ambient generic point, without finiteness or Noetherian assumptions. -/
theorem ambientGenericPoint_height_eq_supportDim {X : Scheme.{u}}
    (W : IntegralClosedSubscheme X) :
    (Order.height (ambientGenericPoint W) : WithBot ℕ∞) =
      topologicalKrullDim W.val.subscheme := by
  rw [Order.height_eq_krullDim_Iic, topologicalKrullDim_eq_pointKrullDim]
  exact (Order.krullDim_eq_of_orderIso (integralSubschemePointOrderIso W)).symm

/-- The same formula for the actual reduced closure of a point. -/
theorem point_height_eq_supportDim (X : Scheme.{u}) (x : X) :
    (Order.height x : WithBot ℕ∞) =
      topologicalKrullDim (pointSupport X x).val.subscheme := by
  simpa only [ambientGenericPoint_pointSupport] using
    ambientGenericPoint_height_eq_supportDim (pointSupport X x)

/-- A finite-dimensional ambient scheme gives finite point heights. -/
theorem point_height_ne_top (X : Scheme.{u})
    (hdim : topologicalKrullDim X < ⊤) (x : X) : Order.height x ≠ ⊤ := by
  have h := (Order.height_le_krullDim x).trans_lt
    ((topologicalKrullDim_eq_pointKrullDim X) ▸ hdim)
  exact (WithBot.coe_lt_coe.mp h).ne

/-- Conversion to a natural number loses no dimension when the ambient
scheme is finite-dimensional. -/
theorem point_height_toNat_eq (X : Scheme.{u})
    (hdim : topologicalKrullDim X < ⊤) (x : X) :
    ((Order.height x).toNat : WithBot ℕ∞) =
      topologicalKrullDim (pointSupport X x).val.subscheme := by
  rw [← point_height_eq_supportDim]
  exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
    (ENat.coe_toNat (point_height_ne_top X hdim x))

/-- The finite integer-valued closure-dimension function is strictly
monotone. This alone does not make it a dimension function. -/
theorem point_height_toNat_strictMono (X : Scheme.{u})
    (hdim : topologicalKrullDim X < ⊤) :
    StrictMono (fun x : X ↦ ((Order.height x).toNat : ℤ)) := by
  intro x y hxy
  have h := Order.height_strictMono hxy (lt_top_iff_ne_top.mpr (point_height_ne_top X hdim x))
  rw [← ENat.coe_toNat (point_height_ne_top X hdim x),
    ← ENat.coe_toNat (point_height_ne_top X hdim y)] at h
  change ((Order.height x).toNat : ℤ) < ((Order.height y).toNat : ℤ)
  exact_mod_cast h

end

end HodgeConjecture.SchemeCycles
