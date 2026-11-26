module

public import HodgeConjecture.Geometry.ProjectiveLineSquare
public import HodgeConjecture.Realization.Betti.Examples.CircleSquare
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisNaturality
public import HodgeConjecture.Realization.Betti.Scheme

@[expose] public section

/-!
# Native singular pullback of the connected projective-line square map

The self-map on the original projective-line point space is composition
of the original scheme section with the actual scheme square morphism.
Its conjugacy with the canonical analytic scheme-point map is proved.
The two chart formulas give a map of the original analytic cover. Actual
circle inclusion, the independently proved circle square calculation and
native Mayer--Vietoris naturality prove multiplication by two on H².
No cycle-class map is used to define or calculate this pullback.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquarePullback

open AlgebraicGeometry CategoryTheory HomologicalComplex
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

abbrev space : TopCat := TopCat.of Point
abbrev lineStructure := projectiveLine ℂ ↘ Spec (.of ℂ)

/-- The original scheme square map acting on the original actual sections. -/
def pointSquareFun (p : Point) : Point :=
  ⟨schemeMorphism p ≫ ProjectiveLineSquare.square ℂ, by
    rw [Category.assoc, ProjectiveLineSquare.over_base, schemeMorphism_toBase]⟩

@[simp]
theorem pointSquareFun_schemeMorphism (p : Point) :
    schemeMorphism (pointSquareFun p) =
      schemeMorphism p ≫ ProjectiveLineSquare.square ℂ := rfl

def canonicalSquareMap : SchemeBetti.space lineStructure ⟶ SchemeBetti.space lineStructure :=
  SchemeBetti.map (ProjectiveLineSquare.square ℂ) (ProjectiveLineSquare.over_base ℂ)

def canonicalMap : space ⟶ SchemeBetti.space lineStructure :=
  TopCat.ofHom ⟨canonicalHomeomorph, canonicalHomeomorph.continuous_toFun⟩

theorem continuous_pointSquareFun : Continuous pointSquareFun := by
  exact canonicalHomeomorph.symm.continuous_toFun.comp
    (canonicalSquareMap.hom.continuous.comp canonicalHomeomorph.continuous_toFun)

/-- This continuous map retains the actual underlying section composition. -/
def pointSquare : C(Point, Point) := ⟨pointSquareFun, continuous_pointSquareFun⟩

def pointMap : space ⟶ space := TopCat.ofHom pointSquare

/-- The fixed old point topology and the canonical scheme-point topology
identify the same original geometric square map. -/
theorem canonicalSquare_naturality :
    canonicalMap ≫ canonicalSquareMap = pointMap ≫ canonicalMap := by
  ext p : 1
  apply Scheme.ComplexPoints.ext
  rfl

theorem canonicalMap_pullback_injective (n : ℕ) :
    Function.Injective (SingularCochains.cohomologyPullback canonicalMap n) :=
  (SingularHomotopy.homeomorphIso canonicalHomeomorph n).toLinearEquiv.injective

@[simp]
theorem pointSquare_finite (z : ℂ) : pointSquare (finite z) = finite (z ^ 2) := by
  apply ProjectiveLineComplexPoints.ext
  change ProjectiveLineSquare.finiteSection ℂ z ≫ ProjectiveLineSquare.square ℂ =
    ProjectiveLineSquare.finiteSection ℂ (z ^ 2)
  exact ProjectiveLineSquare.finiteSection_square ℂ z

@[simp]
theorem pointSquare_reciprocal (z : ℂ) : pointSquare (reciprocal z) = reciprocal (z ^ 2) := by
  apply ProjectiveLineComplexPoints.ext
  change ProjectiveLineSquare.reciprocalSection ℂ z ≫ ProjectiveLineSquare.square ℂ =
    ProjectiveLineSquare.reciprocalSection ℂ (z ^ 2)
  exact ProjectiveLineSquare.reciprocalSection_square ℂ z

@[simp]
theorem pointMap_finite (z : ℂ) : pointMap (finite z) = finite (z ^ 2) :=
  pointSquare_finite z

@[simp]
theorem pointMap_zero : pointMap (finite 0) = finite 0 := by
  rw [pointMap_finite]
  simp

theorem mapsTo_finiteOpen : Set.MapsTo pointMap finiteOpen finiteOpen := by
  rintro _ ⟨z, rfl⟩
  change pointSquare (finite z) ∈ finiteOpen
  rw [pointSquare_finite]
  exact ⟨z ^ 2, rfl⟩

theorem mapsTo_reciprocalOpen : Set.MapsTo pointMap reciprocalOpen reciprocalOpen := by
  rintro _ ⟨z, rfl⟩
  change pointSquare (reciprocal z) ∈ reciprocalOpen
  rw [pointSquare_reciprocal]
  exact ⟨z ^ 2, rfl⟩

/-- The original map on the actual intersection of the two original charts. -/
def overlapMap : TopCat.of ↥(finiteOpen ∩ reciprocalOpen) ⟶
    TopCat.of ↥(finiteOpen ∩ reciprocalOpen) :=
  SingularMayerVietorisNaturality.intersectionMap pointMap
    finiteOpen reciprocalOpen finiteOpen reciprocalOpen mapsTo_finiteOpen mapsTo_reciprocalOpen

theorem overlapMap_coe (z : ↥(finiteOpen ∩ reciprocalOpen)) :
    (overlapMap z : Point) = pointSquare (z : Point) := rfl

/-- The actual inverse of radial normalization, as an original continuous
map into the chart overlap. -/
def circleInclusion : TopCat.of Circle ⟶ TopCat.of ↥(finiteOpen ∩ reciprocalOpen) :=
  TopCat.ofHom overlapCircleHomotopyEquiv.invFun

theorem circleInclusion_coe (z : Circle) : (circleInclusion z : Point) = finite (z : ℂ) := by
  change (overlapHomeomorph (PuncturedComplexCircle.homotopyEquiv.symm z) : Point) = _
  rw [PuncturedComplexCircle.homotopyEquiv_symm_apply, overlapHomeomorph_coe,
    PuncturedComplexCircle.inclusion_coe]

/-- The native H¹ map of actual circle inclusion is an isomorphism, from
the already constructed radial homotopy equivalence. -/
theorem circleInclusion_pullback_injective :
    Function.Injective (SingularCochains.cohomologyPullback circleInclusion 1) :=
  (SingularHomotopy.homotopyEquivIso overlapCircleHomotopyEquiv 1).symm.toLinearEquiv.injective

/-- On the actual unit-circle inclusion the actual chart square is
literally the original circle square map. -/
theorem circleInclusion_square :
    circleInclusion ≫ overlapMap = CircleSquare.squareMap ≫ circleInclusion := by
  ext z : 1
  apply Subtype.ext
  change (overlapMap (circleInclusion z) : Point) =
    (circleInclusion (CircleSquare.squareMap z) : Point)
  rw [overlapMap_coe, circleInclusion_coe, pointSquare_finite, circleInclusion_coe]
  rfl

theorem overlap_cohomologyPullback_square
    (z : SingularCochains.Cohomology (TopCat.of ↥(finiteOpen ∩ reciprocalOpen)) 1) :
    SingularCochains.cohomologyPullback overlapMap 1 z = (2 : ℚ) • z := by
  apply circleInclusion_pullback_injective
  have h := congrArg (fun f ↦ SingularCochains.cohomologyPullback f 1) circleInclusion_square
  rw [SingularCochains.cohomologyPullback_comp,
    SingularCochains.cohomologyPullback_comp] at h
  have hz := congrArg (fun f ↦ f z) h
  change SingularCochains.cohomologyPullback circleInclusion 1
      (SingularCochains.cohomologyPullback overlapMap 1 z) =
    SingularCochains.cohomologyPullback CircleSquare.squareMap 1
      (SingularCochains.cohomologyPullback circleInclusion 1 z) at hz
  rw [CircleSquare.cohomologyPullback_square] at hz
  simpa only [map_smul] using hz

/-- Original continuous pullback on native projective-line H² is computed
by the naturality of the original Mayer--Vietoris connecting isomorphism. -/
theorem cohomologyPullback_square (z : SingularCochains.Cohomology space 2) :
    SingularCochains.cohomologyPullback pointMap 2 z = (2 : ℚ) • z := by
  obtain ⟨w, rfl⟩ := ProjectiveLineSingularCohomology.connectingIso.toLinearEquiv.surjective z
  have h := SingularMayerVietorisNaturality.connecting_naturality pointMap
    finiteOpen reciprocalOpen finiteOpen reciprocalOpen mapsTo_finiteOpen mapsTo_reciprocalOpen
    isOpen_finiteOpen isOpen_reciprocalOpen cover isOpen_finiteOpen isOpen_reciprocalOpen cover 1
  have hw := congrArg (fun f ↦ f w) h
  change SingularCochains.cohomologyPullback pointMap 2
      (ProjectiveLineSingularCohomology.connecting w) =
    ProjectiveLineSingularCohomology.connecting
      (SingularCochains.cohomologyPullback overlapMap 1 w) at hw
  rw [overlap_cohomologyPullback_square, map_smul] at hw
  exact hw

theorem cohomologyPullback_square_eq :
    (SingularCochains.cohomologyPullback pointMap 2).hom = (2 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact cohomologyPullback_square z

/-- The same independently computed degree on the actual canonical
scheme-valued complex-point cohomology, using the proved map conjugacy. -/
theorem canonical_cohomologyPullback_square
    (z : SchemeBetti.Cohomology lineStructure 2) :
    SchemeBetti.pullback (ProjectiveLineSquare.square ℂ)
      (ProjectiveLineSquare.over_base ℂ) 2 z = (2 : ℚ) • z := by
  apply canonicalMap_pullback_injective 2
  have h := congrArg (fun f ↦ SingularCochains.cohomologyPullback f 2) canonicalSquare_naturality
  rw [SingularCochains.cohomologyPullback_comp,
    SingularCochains.cohomologyPullback_comp] at h
  have hz := congrArg (fun f ↦ f z) h
  change SingularCochains.cohomologyPullback canonicalMap 2
      (SchemeBetti.pullback (ProjectiveLineSquare.square ℂ)
        (ProjectiveLineSquare.over_base ℂ) 2 z) =
    SingularCochains.cohomologyPullback pointMap 2
      (SingularCochains.cohomologyPullback canonicalMap 2 z) at hz
  rw [cohomologyPullback_square] at hz
  simpa only [map_smul] using hz

end HodgeConjecture.ProjectiveLineSquarePullback

end
