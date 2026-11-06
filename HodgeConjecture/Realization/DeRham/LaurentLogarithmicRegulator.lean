module

public import HodgeConjecture.Realization.DeRham.LaurentResidue
public import HodgeConjecture.Realization.DeRham.Logarithmic

@[expose] public section

/-!
# A nonzero positive-degree logarithmic de Rham regulator

The actual Kähler residue of the multiplicative line annihilates every
incoming exact form. It therefore descends to degree-one cohomology of the
constructed affine de Rham complex. The class of the original coordinate
unit has residue one, hence is nonzero. The regulator is the general
logarithmic regulator specialized to the actual Laurent coordinate algebra.

This is a de Rham realization of unit symbols in degree one. No identification
with Bloch's higher Chow groups, mixed Hodge structures or singular periods
is assumed or established here.
-/

set_option autoImplicit false

namespace HodgeConjecture.LaurentDeRham

open KaehlerDifferential AffineDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- Residue of actual closed degree-one forms, using the exterior-power coordinates. -/
def closedFormResidue : closedForms k (LaurentPolynomial k) 1 →ₗ[k] k :=
  (kaehlerResidue k).comp
    ((LinearMap.restrictScalars k
      (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).toLinearMap).comp
        (closedForms k (LaurentPolynomial k) 1).subtype)

/-- Every incoming actual differential has residue zero. -/
theorem exactForms_le_ker_closedFormResidue :
    exactForms k (LaurentPolynomial k) 1 ≤ LinearMap.ker (closedFormResidue k) := by
  rw [exactForms_succ]
  rintro _ ⟨ω, rfl⟩
  change kaehlerResidue k
    (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]
      (deRhamDifferential (A := k) 0 ω)) = 0
  have hω := LinearEquiv.symm_apply_apply
    (exteriorPower.zeroEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]) ω
  rw [← hω, differential_zero, kaehlerResidue_D]

/-- The actual residue functional on degree-one cohomology of the constructed complex. -/
def cohomologyResidue : Cohomology k (LaurentPolynomial k) 1 →ₗ[k] k :=
  (exactForms k (LaurentPolynomial k) 1).liftQ (closedFormResidue k)
    (exactForms_le_ker_closedFormResidue k)

@[simp]
theorem cohomologyResidue_class (ω : closedForms k (LaurentPolynomial k) 1) :
    cohomologyResidue k (cohomologyClass k (LaurentPolynomial k) 1 ω) =
      closedFormResidue k ω := rfl

/-- The genuine unit-symbol regulator on the actual multiplicative-line algebra. -/
def regulator : Additive (LaurentPolynomial k)ˣ →+ Cohomology k (LaurentPolynomial k) 1 :=
  logarithmicRegulator k (LaurentPolynomial k)

/-- Its distinguished class is represented by the actual logarithmic differential `T⁻¹ dT`. -/
def coordinateClass : Cohomology k (LaurentPolynomial k) 1 :=
  logarithmicClass k (LaurentPolynomial k) (variableUnit k)

@[simp]
theorem regulator_variableUnit : regulator k (Additive.ofMul (variableUnit k)) =
    coordinateClass k := rfl

/-- Residue detects the coordinate's regulator class with its standard normalization. -/
@[simp]
theorem cohomologyResidue_coordinateClass : cohomologyResidue k (coordinateClass k) = 1 := by
  change closedFormResidue k
    (closedLogarithmicForm k (LaurentPolynomial k) (variableUnit k)) = 1
  change kaehlerResidue k
    (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (logarithmicDifferential k (LaurentPolynomial k) (variableUnit k)))) = 1
  rw [LinearEquiv.apply_symm_apply]
  exact kaehlerResidue_dlogT k

/-- The actual positive-degree cohomology class is nonzero. -/
theorem coordinateClass_ne_zero [Nontrivial k] : coordinateClass k ≠ 0 := by
  intro h
  have hres := congrArg (cohomologyResidue k) h
  rw [cohomologyResidue_coordinateClass, map_zero] at hres
  exact one_ne_zero hres

/-- Thus the unit-symbol regulator is not the zero homomorphism. -/
theorem regulator_ne_zero [Nontrivial k] : regulator k ≠ 0 := by
  intro h
  have hx := DFunLike.congr_fun h (Additive.ofMul (variableUnit k))
  exact coordinateClass_ne_zero k hx

/-- Multiples of the distinguished class give a split copy of the coefficient ring in H¹. -/
def coordinateClassLinearMap : k →ₗ[k] Cohomology k (LaurentPolynomial k) 1 :=
  LinearMap.toSpanSingleton k _ (coordinateClass k)

@[simp]
theorem cohomologyResidue_coordinateClassLinearMap (a : k) :
    cohomologyResidue k (coordinateClassLinearMap k a) = a := by
  change cohomologyResidue k (a • coordinateClass k) = a
  rw [map_smul, cohomologyResidue_coordinateClass, smul_eq_mul, mul_one]

theorem coordinateClassLinearMap_injective : Function.Injective (coordinateClassLinearMap k) := by
  intro a b h
  have hr := congrArg (cohomologyResidue k) h
  simpa only [cohomologyResidue_coordinateClassLinearMap] using hr

theorem cohomologyResidue_surjective : Function.Surjective (cohomologyResidue k) :=
  fun a ↦ ⟨coordinateClassLinearMap k a, cohomologyResidue_coordinateClassLinearMap k a⟩

end

end HodgeConjecture.LaurentDeRham
