module

public import HodgeConjecture.Cycles.ClosedImmersionPushforward
public import HodgeConjecture.Cycles.PointSupport
public import HodgeConjecture.Boundary.Normalization.FiniteFunctionField
public import HodgeConjecture.Boundary.Normalization.FiniteEtaleGluedRefinement

@[expose] public section

/-!
# Degree-weighted pushforward along finite morphisms

The image of an integral support uses the same mapped ideal sheaf as the
closed-immersion construction. Its actual support-to-image morphism is finite
and dominant when the support map is finite. The degree of its actual
function-field extension weights the image cycle; linear extension gives
finite pushforward on the existing cycle module.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem imageIdeal_eq_pointSupport (Z : IntegralClosedSubscheme X) :
    Z.val.map f = (pointSupport Y (f.base (ambientGenericPoint Z))).val := by
  conv_lhs => rw [← pointSupport_ambientGenericPoint Z]
  simp only [pointSupport_val, Scheme.IdealSheafData.map_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure]
  congr 1
  apply SetLike.coe_injective
  simp only [TopologicalSpace.Closeds.coe_closure,
    closure_image_closure f.continuous, Set.image_singleton]

/-- The integral scheme-theoretic image, using exactly the original mapped
ideal sheaf. No finiteness assumption is needed to define this image. -/
def imageSubscheme (Z : IntegralClosedSubscheme X) : IntegralClosedSubscheme Y :=
  ⟨Z.val.map f, by
    rw [imageIdeal_eq_pointSupport f Z]
    exact (pointSupport Y (f.base (ambientGenericPoint Z))).property⟩

@[simp]
theorem imageSubscheme_val (Z : IntegralClosedSubscheme X) :
    (imageSubscheme f Z).val = Z.val.map f := rfl

/-- The general image is the existing closed-immersion image when that
construction applies; the ideal sheaf is not replaced. -/
theorem imageSubscheme_eq_closedImageSubscheme (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    imageSubscheme f Z = closedImageSubscheme f Z :=
  Subtype.ext rfl

/-- The image support has the image of the original ambient generic point. -/
theorem ambientGenericPoint_imageSubscheme (Z : IntegralClosedSubscheme X) :
    ambientGenericPoint (imageSubscheme f Z) = f.base (ambientGenericPoint Z) := by
  have h : imageSubscheme f Z = pointSupport Y (f.base (ambientGenericPoint Z)) :=
    Subtype.ext (imageIdeal_eq_pointSupport f Z)
  rw [h, ambientGenericPoint_pointSupport]

/-- The original support-to-image map is finite whenever the support map is
finite. Its dominance is already supplied by the scheme-theoretic image API. -/
theorem finiteImage_toImage_isFinite (Z : IntegralClosedSubscheme X)
    [IsFinite (Z.val.subschemeι ≫ f)] : IsFinite (Z.val.subschemeι ≫ f).toImage := by
  letI : IsFinite ((Z.val.subschemeι ≫ f).toImage ≫ (Z.val.subschemeι ≫ f).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  exact CollisionFoundations.isFinite_of_comp_of_isSeparated
    (Z.val.subschemeι ≫ f).toImage (Z.val.subschemeι ≫ f).imageι

/-- The finite degree of the actual function-field extension from a support
to its actual image. -/
def finitePushforwardDegree (Z : IntegralClosedSubscheme X)
    [IsFinite (Z.val.subschemeι ≫ f)] : ℕ := by
  letI := Z.property
  letI := (imageSubscheme f Z).property
  letI : IsIntegral (Z.val.subschemeι ≫ f).image := (imageSubscheme f Z).property
  letI : Algebra (imageSubscheme f Z).val.subscheme.functionField
      Z.val.subscheme.functionField :=
    (functionFieldMapOfDominant (Z.val.subschemeι ≫ f).toImage).hom.toAlgebra
  exact Module.finrank (imageSubscheme f Z).val.subscheme.functionField
    Z.val.subscheme.functionField

/-- The actual finite field degree is positive. -/
theorem finitePushforwardDegree_pos (Z : IntegralClosedSubscheme X)
    [IsFinite (Z.val.subschemeι ≫ f)] : 0 < finitePushforwardDegree f Z := by
  letI := Z.property
  letI := (imageSubscheme f Z).property
  letI : IsIntegral (Z.val.subschemeι ≫ f).image := (imageSubscheme f Z).property
  letI := finiteImage_toImage_isFinite f Z
  letI : Algebra (imageSubscheme f Z).val.subscheme.functionField
      Z.val.subscheme.functionField :=
    (functionFieldMapOfDominant (Z.val.subschemeι ≫ f).toImage).hom.toAlgebra
  letI : FiniteDimensional (imageSubscheme f Z).val.subscheme.functionField
      Z.val.subscheme.functionField :=
    CollisionFoundations.functionFieldMapOfDominant_finiteDimensional
      (Z.val.subschemeι ≫ f).toImage
  exact Module.finrank_pos

/-- The actual image isomorphism for a closed immersion gives degree one. -/
theorem finitePushforwardDegree_of_isClosedImmersion (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] : finitePushforwardDegree f Z = 1 := by
  letI := Z.property
  letI := (imageSubscheme f Z).property
  letI : IsIntegral (Z.val.subschemeι ≫ f).image := (imageSubscheme f Z).property
  letI : Algebra (imageSubscheme f Z).val.subscheme.functionField
      Z.val.subscheme.functionField :=
    (functionFieldMapOfDominant (Z.val.subschemeι ≫ f).toImage).hom.toAlgebra
  have hsurj : Function.Surjective (functionFieldMapOfDominant (Z.val.subschemeι ≫ f).toImage) := by
    rw [functionFieldMapOfDominant_eq_openImmersion]
    exact (functionFieldIsoOfOpenImmersion (Z.val.subschemeι ≫ f).toImage).commRingCatIsoToRingEquiv.surjective
  apply finrank_eq_one (1 : Z.val.subscheme.functionField) one_ne_zero
  intro x
  obtain ⟨c, rfl⟩ := hsurj x
  refine ⟨c, ?_⟩
  change functionFieldMapOfDominant (Z.val.subschemeι ≫ f).toImage c * 1 = _
  rw [mul_one]

/-- Degree-weighted pushforward on the existing finite, ungraded cycle module. -/
def finitePushforward (R : Type v) [Semiring R] (f : X ⟶ Y) [IsFinite f] :
    Cycles X R →ₗ[R] Cycles Y R :=
  Finsupp.linearCombination R (fun Z ↦
    finitePushforwardDegree f Z • fundamentalCycle R (imageSubscheme f Z))

variable (R : Type v) [Semiring R]

@[simp]
theorem finitePushforward_single [IsFinite f] (Z : IntegralClosedSubscheme X) (r : R) :
    finitePushforward R f (Finsupp.single Z r) =
      r • (finitePushforwardDegree f Z • fundamentalCycle R (imageSubscheme f Z)) := by
  simp [finitePushforward]

/-- A fundamental cycle maps to the original image with its actual field degree. -/
@[simp]
theorem finitePushforward_fundamentalCycle [IsFinite f] (Z : IntegralClosedSubscheme X) :
    finitePushforward R f (fundamentalCycle R Z) =
      finitePushforwardDegree f Z • fundamentalCycle R (imageSubscheme f Z) := by
  simp [fundamentalCycle]

/-- Finite pushforward extends the existing coefficient-one closed-immersion map. -/
theorem finitePushforward_eq_closedImmersionPushforward [IsClosedImmersion f] :
    finitePushforward R f = closedImmersionPushforward R f := by
  apply Finsupp.lhom_ext
  intro Z r
  simp only [finitePushforward_single, closedImmersionPushforward_single,
    finitePushforwardDegree_of_isClosedImmersion, one_smul,
    imageSubscheme_eq_closedImageSubscheme, closedImageCycle]

@[simp]
theorem finitePushforward_id : finitePushforward R (𝟙 X) = LinearMap.id := by
  rw [finitePushforward_eq_closedImmersionPushforward, closedImmersionPushforward_id]

end

end HodgeConjecture.SchemeCycles
