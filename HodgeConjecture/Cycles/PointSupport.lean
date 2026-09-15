import HodgeConjecture.Cycles.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Actual integral closed supports of scheme points

The reduced induced closed subscheme on the closure of a point is integral.
Conversely an integral closed subscheme is recovered from its ambient
generic point. These constructions identify the points of an arbitrary
scheme with its actual integral closed subschemes, without an integrality,
Noetherianity, or dimension assumption on the ambient scheme.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : Scheme.{u}}

/-- The vanishing ideal gives the actual reduced induced scheme structure
on a closed subset. -/
theorem vanishingIdeal_subscheme_isReduced (X : Scheme.{u}) (C : Closeds X) :
    AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal C
  apply (config := { allowSynthFailures := true }) isReduced_of_isReduced_stalk
  intro x
  obtain ⟨y, hy⟩ := I.subschemeCover.covers x
  let U : X.affineOpens := I.subschemeCover.idx x
  haveI : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (by
      change (PrimeSpectrum.vanishingIdeal _).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _)
  haveI : AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X U)) := by
    change AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  rw [← hy]
  exact _root_.isReduced_of_injective ((I.subschemeCover.f U).stalkMap y).hom
    (asIso ((I.subschemeCover.f U).stalkMap y)).commRingCatIsoToRingEquiv.injective

/-- The defining ideal of a reduced closed subscheme is radical. -/
theorem radical_eq_of_subscheme_isReduced (I : X.IdealSheafData)
    [AlgebraicGeometry.IsReduced I.subscheme] : I.radical = I := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, ← I.ker_subschemeι_app U]
  exact Ideal.radical_eq_iff.mpr
    ((RingHom.ker_isRadical_iff_reduced_of_surjective
      (I.subschemeι_app_surjective U)).mpr inferInstance)

/-- The reduced closure of a point, as an actual integral ideal-sheaf subscheme. -/
def pointSupport (X : Scheme.{u}) (x : X) : IntegralClosedSubscheme X := by
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  refine ⟨I, ?_⟩
  letI : AlgebraicGeometry.IsReduced I.subscheme :=
    vanishingIdeal_subscheme_isReduced X (Closeds.closure {x})
  have hI : IsIrreducible (I.support : Set X) := by
    simpa only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure] using
        (isIrreducible_singleton : IsIrreducible ({x} : Set X)).closure
  letI : IrreducibleSpace I.subscheme := Subtype.irreducibleSpace hI
  exact isIntegral_of_irreducibleSpace_of_isReduced _

@[simp]
theorem pointSupport_val (X : Scheme.{u}) (x : X) :
    (pointSupport X x).val =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) := rfl

@[simp]
theorem pointSupport_support (X : Scheme.{u}) (x : X) :
    (pointSupport X x).val.support = Closeds.closure ({x} : Set X) := by
  ext y
  rfl

/-- The generic point of the actual integral subscheme, mapped into its ambient scheme. -/
def ambientGenericPoint (Z : IntegralClosedSubscheme X) : X :=
  letI := Z.property
  Z.val.subschemeι.base (genericPoint Z.val.subscheme)

/-- The ambient generic point has exactly the closed support of the integral subscheme. -/
theorem ambientGenericPoint_isGenericPoint (Z : IntegralClosedSubscheme X) :
    IsGenericPoint (ambientGenericPoint Z) (Z.val.support : Set X) := by
  letI := Z.property
  have h := (genericPoint_spec Z.val.subscheme).image Z.val.subschemeι.continuous
  simpa only [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
    Z.val.support.isClosed.closure_eq] using h

@[simp]
theorem ambientGenericPoint_pointSupport (X : Scheme.{u}) (x : X) :
    ambientGenericPoint (pointSupport X x) = x := by
  apply (ambientGenericPoint_isGenericPoint (pointSupport X x)).eq
  simpa only [pointSupport_support, Closeds.coe_closure] using
    (isGenericPoint_closure : IsGenericPoint x (closure ({x} : Set X)))

@[simp]
theorem pointSupport_ambientGenericPoint (Z : IntegralClosedSubscheme X) :
    pointSupport X (ambientGenericPoint Z) = Z := by
  letI := Z.property
  apply Subtype.ext
  rw [pointSupport_val]
  have h : Closeds.closure ({ambientGenericPoint Z} : Set X) = Z.val.support :=
    SetLike.coe_injective (ambientGenericPoint_isGenericPoint Z).def
  rw [h, Scheme.IdealSheafData.vanishingIdeal_support, radical_eq_of_subscheme_isReduced]

/-- Scheme points are equivalent to actual integral closed subschemes via
reduced closure and the ambient generic point. -/
def pointEquivIntegralClosedSubscheme (X : Scheme.{u}) : X ≃ IntegralClosedSubscheme X where
  toFun := pointSupport X
  invFun := ambientGenericPoint
  left_inv := ambientGenericPoint_pointSupport X
  right_inv := pointSupport_ambientGenericPoint

end

end HodgeConjecture.SchemeCycles
