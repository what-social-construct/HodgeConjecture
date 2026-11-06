module

public import HodgeConjecture.Cycles.SchemeLocalOrder

@[expose] public section

/-!
# Affine presentations of actual rational functions

On a nonempty affine open of an integral scheme, Mathlib identifies the
actual generic-point stalk with the fraction field of the section ring.
We use that identification to present a nonzero rational function by two
nonzero sections. The section-to-field map factors through each actual
local stalk, and sections outside the chart prime give unit germs.

Consequently the existing signed local coefficient vanishes wherever both
sections avoid the prime. No normality or finite-support conclusion is
assumed here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- A rational function on any nonempty affine open is an actual fraction
of nonzero sections, using the canonical map to the generic stalk. -/
theorem exists_affine_fraction (X : Scheme.{u}) [IsIntegral X]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] (f : X.functionFieldˣ) :
    ∃ a b : Γ(X, U), a ≠ 0 ∧ b ≠ 0 ∧
      (f : X.functionField) =
        algebraMap Γ(X, U) X.functionField a / algebraMap Γ(X, U) X.functionField b := by
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, hb, hf⟩ := IsFractionRing.div_surjective (A := Γ(X, U))
    (f : X.functionField)
  refine ⟨a, b, ?_, mem_nonZeroDivisors_iff_ne_zero.mp hb, hf.symm⟩
  intro ha
  apply f.ne_zero
  rw [← hf, ha, map_zero, zero_div]

/-- The canonical section-to-function-field map is the composite through
the actual germ at any point of the open. -/
theorem sectionToFunctionField_through_stalk (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (x : U) (a : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x.val) X.functionField
        ((X.presheaf.germ U x.val x.property).hom a) =
      algebraMap Γ(X, U) X.functionField a := by
  letI := X.presheaf.algebra_section_stalk x
  exact (IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x.val)
    X.functionField a).symm

/-- Actual germs on an affine chart are units exactly outside the chart's
prime ideal. This does not require an integral ambient scheme. -/
theorem affineGerm_isUnit_iff (X : Scheme.{u}) {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (a : Γ(X, U)) :
    IsUnit ((X.presheaf.germ U x.val x.property).hom a) ↔
      a ∉ (hU.primeIdealOf x).asIdeal := by
  letI := X.presheaf.algebra_section_stalk x
  letI := hU.isLocalization_stalk x
  exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x.val)
    (hU.primeIdealOf x).asIdeal a

/-- A fraction of sections that are both units at a divisor point has
zero signed local coefficient. This is the existing local order, not a
new coefficient or a support hypothesis. -/
theorem divisorOrder_eq_zero_of_affine_fraction (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] (x : DivisorPoint X) (hx : x.val ∈ U)
    (f : X.functionFieldˣ) (a b : Γ(X, U))
    (hf : (f : X.functionField) =
      algebraMap Γ(X, U) X.functionField a / algebraMap Γ(X, U) X.functionField b)
    (hnot_a : a ∉ (hU.primeIdealOf ⟨x.val, hx⟩).asIdeal)
    (hnot_b : b ∉ (hU.primeIdealOf ⟨x.val, hx⟩).asIdeal) :
    divisorOrder X x f = 0 := by
  obtain ⟨ua, hua⟩ := (affineGerm_isUnit_iff X hU ⟨x.val, hx⟩ a).mpr hnot_a
  obtain ⟨ub, hub⟩ := (affineGerm_isUnit_iff X hU ⟨x.val, hx⟩ b).mpr hnot_b
  have hf' : f =
      Units.map (algebraMap (X.presheaf.stalk x.val) X.functionField).toMonoidHom ua /
        Units.map (algebraMap (X.presheaf.stalk x.val) X.functionField).toMonoidHom ub := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.coe_map]
    change (f : X.functionField) =
      algebraMap (X.presheaf.stalk x.val) X.functionField (ua : X.presheaf.stalk x.val) /
        algebraMap (X.presheaf.stalk x.val) X.functionField (ub : X.presheaf.stalk x.val)
    rw [hua, hub, sectionToFunctionField_through_stalk X U ⟨x.val, hx⟩ a,
      sectionToFunctionField_through_stalk X U ⟨x.val, hx⟩ b]
    exact hf
  change localOrder (X.presheaf.stalk x.val) f = 0
  rw [hf', localOrder_div, localOrder_map_unit, localOrder_map_unit, sub_self]

end

end HodgeConjecture.SchemeCycles
