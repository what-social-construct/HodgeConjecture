module

public import HodgeConjecture.Geometry.ProjectiveLineProperties
public import HodgeConjecture.Cycles.FunctionFieldComparison
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public noncomputable section

/-!
# Actual projective-line function fields and the chart inversion

Both chart readings are the original generic-stalk isomorphisms of the
actual open immersions. Their agreement on the actual Laurent overlap
forces the comparison to fix constants and send X to its inverse. No
coordinate automorphism or function-field comparison is supplied as input.

Selected local adaptation from AxiomMath/Stacks revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardPrincipal/`:
`ProjectiveLineFunctionField.lean` and the geometric part of
`ProjectiveLineInfinity.lean`. Apache-2.0; see `third_party/axiom-stacks/LICENSE`.
The generic-stalk maps and their functoriality reuse the existing project API.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory HodgeConjecture.SchemeCycles

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

instance algebra_polynomial_affineLine_functionField :
    Algebra (Polynomial k) ((Spec (.of (Polynomial k))).functionField) :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial k))

instance isFractionRing_polynomial_affineLine_functionField :
    IsFractionRing (Polynomial k) ((Spec (.of (Polynomial k))).functionField) :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial k))

/-- The canonical fraction-field reading of the actual polynomial spectrum. -/
def affineLineFunctionFieldEquiv :
    (Spec (.of (Polynomial k))).functionField ≃ₐ[Polynomial k] RatFunc k :=
  IsLocalization.algEquiv (nonZeroDivisors (Polynomial k)) _ _

/-- The x-chart reading is induced by its actual open-immersion stalk map. -/
def projectiveLineFunctionFieldEquiv : (projectiveLine k).functionField ≃+* RatFunc k :=
  (functionFieldEquivOfOpenImmersion (projectiveLineXChart k)).trans
    (affineLineFunctionFieldEquiv k).toRingEquiv

instance algebra_laurentPolynomial_functionField :
    Algebra (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField) :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (LaurentPolynomial k))

/-- The actual generic-stalk map, read as a ring homomorphism. -/
abbrev fieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : Y.functionField →+* X.functionField :=
  (functionFieldMapOfDominant f).hom

private theorem fieldMap_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) : fieldMap f = fieldMap g := by
  subst h
  rfl

private theorem fieldMap_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [IsDominant g] : fieldMap (f ≫ g) = (fieldMap f).comp (fieldMap g) :=
  congrArg CommRingCat.Hom.hom (functionFieldMapOfDominant_comp g f)

/-- The actual inverse-coordinate ring restriction defining the second overlap inclusion. -/
def projectiveLineOverlapInverseCoordinate : Polynomial k →ₐ[k] LaurentPolynomial k :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

/-- The inverse-coordinate ring map induces the original geometric overlap inclusion. -/
theorem projectiveLineOverlapYInclusion_eq_specMap :
    projectiveLineOverlapYInclusion k =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) := by
  rw [← Spec.map_preimage (projectiveLineOverlapYInclusion k)]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp [projectiveLineOverlapYInclusion, projectiveLinePuncturedChart,
      projectiveLineInversionIso, projectiveLineOverlapInverseCoordinate]
  · simp [projectiveLineOverlapYInclusion, projectiveLinePuncturedChart,
      projectiveLineInversionIso, projectiveLineOverlapInverseCoordinate]

/-- The function field of the second chart, read on the overlap, sends a polynomial to the
corresponding Laurent polynomial in `T⁻¹`. -/
theorem dominantFunctionFieldMap_overlapYInclusion_algebraMap (a : Polynomial k) :
    fieldMap (projectiveLineOverlapYInclusion k)
        (algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a) =
      algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (projectiveLineOverlapInverseCoordinate k a) :=
  by
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (projectiveLineOverlapInverseCoordinate k).toRingHom)) := by
      rw [← projectiveLineOverlapYInclusion_eq_specMap]
      infer_instance
    have hmap := fieldMap_congr _ _ (projectiveLineOverlapYInclusion_eq_specMap k)
    rw [hmap]
    exact functionFieldMapOfDominant_spec_algebraMap
      (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) a

/-- The function field of the first chart, read on the overlap, sends a polynomial to the
corresponding Laurent polynomial in `T`. -/
theorem dominantFunctionFieldMap_puncturedChart_algebraMap (a : Polynomial k) :
    fieldMap (projectiveLinePuncturedChart k)
        (algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a) =
      algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (Polynomial.toLaurent a) :=
  functionFieldMapOfDominant_spec_algebraMap
    (CommRingCat.ofHom (Polynomial.toLaurent (R := k))) a

/-- **The two charts agree on the overlap.** The two routes from the function field of the
projective line to the function field of the overlap `Spec k[T, T⁻¹]` coincide, because the
square `AlgebraicGeometry.isPullback_projectiveLineCharts` commutes and
`AlgebraicGeometry.dominantFunctionFieldMap` is contravariantly functorial. -/
theorem dominantFunctionFieldMap_chart_overlap_eq (w : (projectiveLine k).functionField) :
    fieldMap (projectiveLinePuncturedChart k)
        (fieldMap (projectiveLineXChart k) w) =
      fieldMap (projectiveLineOverlapYInclusion k)
        (fieldMap (projectiveLineYChart k) w) := by
  have hsquare : projectiveLinePuncturedChart k ≫ projectiveLineXChart k =
      projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k := by
    simpa only [projectiveLineOverlapYInclusion, Category.assoc] using
      projectiveLineOverlap_compat k
  have h := fieldMap_congr _ _ hsquare
  rw [fieldMap_comp, fieldMap_comp] at h
  exact RingHom.congr_fun h w

private theorem overlapYInclusion_functionField_injective :
    Function.Injective (fieldMap (projectiveLineOverlapYInclusion k)) :=
  RingHom.injective _

/-- The second chart reads a constant rational function as the same constant. -/
theorem dominantFunctionFieldMap_yChart_C (c : k) (w : (projectiveLine k).functionField)
    (hw : fieldMap (projectiveLineXChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) (Polynomial.C c)) :
    fieldMap (projectiveLineYChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) (Polynomial.C c) := by
  refine overlapYInclusion_functionField_injective k ?_
  rw [dominantFunctionFieldMap_overlapYInclusion_algebraMap,
    ← dominantFunctionFieldMap_chart_overlap_eq, hw,
    dominantFunctionFieldMap_puncturedChart_algebraMap]
  congr 1
  simp [projectiveLineOverlapInverseCoordinate]

/-- **The transition inverts the coordinate.** The second chart reads the coordinate of the first
as its inverse, which is the substitution `x ↦ x⁻¹` gluing the two charts. -/
theorem dominantFunctionFieldMap_yChart_X (w : (projectiveLine k).functionField)
    (hw : fieldMap (projectiveLineXChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) Polynomial.X) :
    fieldMap (projectiveLineYChart k) w =
      (algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) Polynomial.X)⁻¹ := by
  refine overlapYInclusion_functionField_injective k ?_
  have hT : (algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (LaurentPolynomial.T (-1 : ℤ)))⁻¹ =
      algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (LaurentPolynomial.T (1 : ℤ)) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, ← LaurentPolynomial.T_add]
    simp
  rw [map_inv₀, dominantFunctionFieldMap_overlapYInclusion_algebraMap,
    ← dominantFunctionFieldMap_chart_overlap_eq, hw,
    dominantFunctionFieldMap_puncturedChart_algebraMap,
    show projectiveLineOverlapInverseCoordinate k Polynomial.X = LaurentPolynomial.T (-1 : ℤ) by
      simp [projectiveLineOverlapInverseCoordinate],
    hT]
  congr 1
  simp

/-! ### The inversion on the rational function field -/

/-- The function field of the projective line, identified with that of the second chart. -/
def projectiveLineFunctionFieldEquivY :
    (projectiveLine k).functionField ≃+* (Spec (.of (Polynomial k))).functionField :=
  functionFieldEquivOfOpenImmersion (projectiveLineYChart k)

/-- **The inversion gluing the two charts of the projective line**, read on `RatFunc k` through
the identification coming from the first chart: the automorphism sending a rational function to
the same function written in the coordinate of the second chart. -/
def projectiveLineChartInversion : RatFunc k ≃+* RatFunc k :=
  ((projectiveLineFunctionFieldEquiv k).symm.trans (projectiveLineFunctionFieldEquivY k)).trans
    (affineLineFunctionFieldEquiv k).toRingEquiv

/-- The inversion is the comparison of the two chart identifications of the function field. -/
theorem projectiveLineChartInversion_apply (g : (projectiveLine k).functionField) :
    projectiveLineChartInversion k (projectiveLineFunctionFieldEquiv k g) =
      affineLineFunctionFieldEquiv k (projectiveLineFunctionFieldEquivY k g) := by
  simp [projectiveLineChartInversion]

private theorem xChart_eq_of_equiv (a : Polynomial k) (w : (projectiveLine k).functionField)
    (hw : projectiveLineFunctionFieldEquiv k w = algebraMap (Polynomial k) (RatFunc k) a) :
    fieldMap (projectiveLineXChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a := by
  refine (affineLineFunctionFieldEquiv k).injective ?_
  rwa [AlgEquiv.commutes]

private theorem chartInversion_algebraMap_eq (a : Polynomial k)
    (y : (Spec (.of (Polynomial k))).functionField)
    (h : ∀ w : (projectiveLine k).functionField,
      fieldMap (projectiveLineXChart k) w =
        algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a →
      fieldMap (projectiveLineYChart k) w = y) :
    projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) a) =
      affineLineFunctionFieldEquiv k y := by
  obtain ⟨w, hw⟩ := (projectiveLineFunctionFieldEquiv k).surjective
    (algebraMap (Polynomial k) (RatFunc k) a)
  rw [← hw, projectiveLineChartInversion_apply, ← h w (xChart_eq_of_equiv k a w hw)]
  rfl

/-- The inversion fixes the constants. -/
theorem projectiveLineChartInversion_C (c : k) :
    projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) =
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c) := by
  rw [chartInversion_algebraMap_eq k _ _ (dominantFunctionFieldMap_yChart_C k c),
    AlgEquiv.commutes]

/-- The inversion sends the coordinate to its inverse. -/
theorem projectiveLineChartInversion_X :
    projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) =
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)⁻¹ := by
  rw [chartInversion_algebraMap_eq k _ _ (dominantFunctionFieldMap_yChart_X k), map_inv₀,
    AlgEquiv.commutes]


end AlgebraicGeometry

end
