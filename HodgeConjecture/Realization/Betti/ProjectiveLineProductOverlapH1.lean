module

public import HodgeConjecture.Realization.Betti.ProjectiveLineDegreeOne
public import HodgeConjecture.Realization.Betti.Circle
public import HodgeConjecture.Realization.Betti.ProductContractibleFactor

/-!
# First cohomology on the punctured-coordinate product

The punctured complex coordinate has a proved rational H¹ coordinate through
its radial homotopy equivalence with the circle. Its pullback to the product
with the projective line is nonzero, witnessed by a fixed point of the second
factor. A Mayer–Vietoris calculation on the two charts of the second factor
will show that this pullback generates the full product H¹.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductOverlapH1

open CategoryTheory ContinuousMap

abbrev Plane := PuncturedComplexCircle.Plane
abbrev LinePoint := ProjectiveLineComplexPoints.Point
abbrev PlaneH1 := SingularCochains.Cohomology (TopCat.of Plane) 1
abbrev ProductH1 := SingularCochains.Cohomology (TopCat.of (Plane × LinePoint)) 1

/-- The original punctured-plane H¹ coordinate through the native circle. -/
def planeH1Coordinate : PlaneH1 ≃ₗ[ℚ] ℚ :=
  (SingularHomotopy.homotopyEquivIso PuncturedComplexCircle.homotopyEquiv 1).toLinearEquiv.symm.trans
    CircleCohomology.h1Equiv

/-- The pullback of the actual circle cover class to the punctured plane. -/
def planeGenerator : PlaneH1 :=
  (SingularHomotopy.homotopyEquivIso PuncturedComplexCircle.homotopyEquiv 1).hom
    CircleCohomology.coverGenerator

@[simp] theorem planeH1Coordinate_generator : planeH1Coordinate planeGenerator = 1 := by
  let e := (SingularHomotopy.homotopyEquivIso
    PuncturedComplexCircle.homotopyEquiv 1).toLinearEquiv
  change CircleCohomology.h1Equiv
    (e.symm (e CircleCohomology.coverGenerator)) = 1
  rw [LinearEquiv.symm_apply_apply, CircleCohomology.h1Equiv_coverGenerator]

theorem planeGenerator_ne_zero : planeGenerator ≠ 0 := by
  intro h
  have := planeH1Coordinate_generator
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem planeH1_generated (z : PlaneH1) :
    ∃ a : ℚ, z = a • planeGenerator := by
  refine ⟨planeH1Coordinate z, ?_⟩
  apply planeH1Coordinate.injective
  rw [map_smul, planeH1Coordinate_generator, smul_eq_mul, mul_one]

/-- Projection of the punctured-coordinate product to its first factor. -/
def planeProjection : TopCat.of (Plane × LinePoint) ⟶ TopCat.of Plane :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- A fixed second-coordinate point gives an actual section of projection. -/
def planeSection : TopCat.of Plane ⟶ TopCat.of (Plane × LinePoint) :=
  TopCat.ofHom ⟨fun z => (z, ProjectiveLineComplexPoints.finite 0),
    continuous_id.prodMk continuous_const⟩

@[simp] theorem planeSection_projection :
    planeSection ≫ planeProjection = 𝟙 (TopCat.of Plane) := by
  ext z
  rfl

/-- Projection pullback is injective because the displayed continuous
section pulls back to the identity in singular cohomology. -/
theorem planeProjection_pullback_injective :
    Function.Injective (SingularCochains.cohomologyPullback planeProjection 1) := by
  intro x y hxy
  have h := congrArg
    (fun z : ProductH1 =>
      SingularCochains.cohomologyPullback planeSection 1 z) hxy
  simpa only [← ModuleCat.comp_apply, ← SingularCochains.cohomologyPullback_comp,
    planeSection_projection, SingularCochains.cohomologyPullback_id,
    ModuleCat.id_apply] using h

/-- The base punctured-plane class stays nonzero on the product. -/
theorem planeGenerator_product_ne_zero :
    SingularCochains.cohomologyPullback planeProjection 1 planeGenerator ≠ 0 := by
  intro h
  apply planeGenerator_ne_zero
  apply planeProjection_pullback_injective
  simpa only [map_zero] using h

end HodgeConjecture.ProjectiveLineProductOverlapH1

end
