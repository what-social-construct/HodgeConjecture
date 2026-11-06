module

public import HodgeConjecture.Cycles.FlatComponents
public import HodgeConjecture.Cycles.SchemeLocalOrder

@[expose] public section

/-! Pullback of an actual rational function to an existing reduced
component, and its quotient-length formula at a divisor point. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The actual generic-stalk homomorphism to a reduced source component of a flat map. -/
def flatComponentFunctionFieldMap {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] (W : irreducibleComponents X) :
    letI := (pointSupport X W.2.1.genericPoint).property
    Y.functionField ⟶ (pointSupport X W.2.1.genericPoint).val.subscheme.functionField := by
  letI := (pointSupport X W.2.1.genericPoint).property
  letI := pointSupport_component_isDominant_comp f W
  exact functionFieldMapOfDominant ((pointSupport X W.2.1.genericPoint).val.subschemeι ≫ f)

/-- A nonzero rational function admits a nonzero numerator and denominator in the original
local ring at every point. -/
theorem exists_local_fraction {X : Scheme.{u}} [IsIntegral X] (x : X)
    (g : X.functionFieldˣ) :
    ∃ (a b : X.presheaf.stalk x) (ha : a ≠ 0) (hb : b ≠ 0),
      Units.mk0 (algebraMap (X.presheaf.stalk x) X.functionField a)
          (by simpa only [map_zero] using
            (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne ha) /
        Units.mk0 (algebraMap (X.presheaf.stalk x) X.functionField b)
          (by simpa only [map_zero] using
            (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne hb) = g := by
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x)
    (g : X.functionField)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, zero_div] at hfrac
    exact g.ne_zero hfrac.symm
  exact ⟨a, b, ha0, hb0, Units.ext hfrac⟩

/-- Actual dominant maps preserve the nonzero local numerator and denominator, and the
divisor order of their field quotient is the difference of their actual quotient lengths. -/
theorem divisorOrder_dominant_fraction {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    [IsLocallyNoetherian T] (h : T ⟶ Y) [IsDominant h] (z : DivisorPoint T)
    (a b : Y.presheaf.stalk (h.base z.val)) (ha : a ≠ 0) (hb : b ≠ 0) :
    divisorOrder T z
      (Units.map (functionFieldMapOfDominant h).hom.toMonoidHom
        (Units.mk0 (algebraMap (Y.presheaf.stalk (h.base z.val)) Y.functionField a)
            (by simpa only [map_zero] using
              (IsFractionRing.injective (Y.presheaf.stalk (h.base z.val)) Y.functionField).ne ha) /
          Units.mk0 (algebraMap (Y.presheaf.stalk (h.base z.val)) Y.functionField b)
            (by simpa only [map_zero] using
              (IsFractionRing.injective (Y.presheaf.stalk (h.base z.val)) Y.functionField).ne hb))) =
      ((Module.length (T.presheaf.stalk z.val)
        ((T.presheaf.stalk z.val) ⧸ Ideal.span {(h.stalkMap z.val).hom a})).toNat : ℤ) -
      ((Module.length (T.presheaf.stalk z.val)
        ((T.presheaf.stalk z.val) ⧸ Ideal.span {(h.stalkMap z.val).hom b})).toNat : ℤ) := by
  have hinj : Function.Injective (h.stalkMap z.val) := by
    intro v w hvw
    apply IsFractionRing.injective (Y.presheaf.stalk (h.base z.val)) Y.functionField
    apply functionFieldMapOfDominant_injective h
    simp only [functionFieldMapOfDominant_algebraMap]
    exact congrArg (algebraMap (T.presheaf.stalk z.val) T.functionField) hvw
  have hne (v : Y.presheaf.stalk (h.base z.val)) (hv : v ≠ 0) :
      (h.stalkMap z.val).hom v ≠ 0 :=
    fun hzero ↦ hv (hinj (by simpa using hzero))
  have hunit (v : Y.presheaf.stalk (h.base z.val)) (hv : v ≠ 0) :
      Units.map (functionFieldMapOfDominant h).hom.toMonoidHom
          (Units.mk0 (algebraMap (Y.presheaf.stalk (h.base z.val)) Y.functionField v)
            (by simpa only [map_zero] using
              (IsFractionRing.injective (Y.presheaf.stalk (h.base z.val)) Y.functionField).ne hv)) =
        Units.mk0 (algebraMap (T.presheaf.stalk z.val) T.functionField
            ((h.stalkMap z.val).hom v))
          (by simpa only [map_zero] using
            (IsFractionRing.injective (T.presheaf.stalk z.val) T.functionField).ne (hne v hv)) :=
    Units.ext (functionFieldMapOfDominant_algebraMap h z.val v)
  rw [map_div, hunit a ha, hunit b hb]
  exact localOrder_fraction (T.presheaf.stalk z.val) _ _ (hne a ha) (hne b hb)

end

end HodgeConjecture.SchemeCycles
