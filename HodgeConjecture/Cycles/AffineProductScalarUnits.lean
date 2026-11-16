module

public import HodgeConjecture.Cycles.BaseFieldScalarPrincipalDivisor
public import HodgeConjecture.Cycles.FunctionFieldComparison
public import HodgeConjecture.Cycles.ProjectiveLineProductFiberCodimension
public import HodgeConjecture.Geometry.ProjectiveLineProductAffineDimension
public import HodgeConjecture.Geometry.AffineComplexPoints
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Units of the complex affine product chart

The tensor-coordinate ring of the product chart is a two-variable
polynomial ring. Every unit is therefore a nonzero complex scalar.
The same scalar is identified in the actual function field of its
spectrum through the chart's structure morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TensorProduct
open HodgeConjecture.SchemeCycles.ProjectiveLineDegree

noncomputable section

abbrev affineProductCoordinateRing := Polynomial ℂ ⊗[ℂ] Polynomial ℂ
local notation "B" => affineProductCoordinateRing

/-- Every unit of the affine product's tensor-coordinate ring is a
nonzero complex scalar. -/
theorem exists_scalar_of_affineProduct_unit (u : Bˣ) :
    ∃ c : ℂˣ, Units.map (algebraMap ℂ B).toMonoidHom c = u := by
  let e := projectiveLineAffineProductRingEquiv ℂ
  have he : IsUnit (e (u : B)) := IsUnit.map e.toRingHom u.isUnit
  obtain ⟨c, hc, hC⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp he
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨cu, ?_⟩
  apply Units.ext
  change algebraMap ℂ B (cu : ℂ) = (u : B)
  apply e.injective
  calc
    e (algebraMap ℂ B (cu : ℂ)) = MvPolynomial.C (cu : ℂ) := by
      simpa using e.commutes (cu : ℂ)
    _ = e (u : B) := by rw [hcu]; exact hC.symm

/-- The function-field image of an affine-product unit is exactly the
base scalar supplied by the actual chart structure morphism. -/
theorem exists_baseScalar_of_affineProduct_specUnit
    (u : Bˣ) :
    letI : Algebra B (Spec (.of B)).functionField := specFunctionFieldAlgebra (.of B)
    letI : Algebra ℂ (Spec (.of ℂ)).functionField := specFunctionFieldAlgebra (.of ℂ)
    let q := AffineComplexPoints.structureMorphism B
    letI : IsDominant q := isDominant_toSpecField ℂ (Spec (.of B)) q
    ∃ c : ℂˣ,
      Units.map (algebraMap B (Spec (.of B)).functionField).toMonoidHom u =
        Units.map (functionFieldMapOfDominant q).hom.toMonoidHom
          (Units.map (algebraMap ℂ (Spec (.of ℂ)).functionField).toMonoidHom c) := by
  letI : Algebra B (Spec (.of B)).functionField := specFunctionFieldAlgebra (.of B)
  letI : Algebra ℂ (Spec (.of ℂ)).functionField := specFunctionFieldAlgebra (.of ℂ)
  let q := AffineComplexPoints.structureMorphism B
  letI : IsDominant q := isDominant_toSpecField ℂ (Spec (.of B)) q
  obtain ⟨c, hc⟩ := exists_scalar_of_affineProduct_unit u
  refine ⟨c, ?_⟩
  rw [← hc]
  apply Units.ext
  change algebraMap B (Spec (.of B)).functionField
      (algebraMap ℂ B (c : ℂ)) =
    (functionFieldMapOfDominant q).hom
      (algebraMap ℂ (Spec (.of ℂ)).functionField (c : ℂ))
  exact (functionFieldMapOfDominant_spec_algebraMap
    (f := CommRingCat.ofHom (algebraMap ℂ B)) (c : ℂ)).symm

end

end HodgeConjecture.SchemeCycles

end
