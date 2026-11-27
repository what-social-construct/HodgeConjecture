module

public import HodgeConjecture.Realization.Betti.Examples.ComplexPointThom
public import HodgeConjecture.Realization.Betti.Examples.CircleSquare
public import HodgeConjecture.Realization.Betti.RelativeCochainsNaturality

@[expose] public section

/-!
# The actual local ramified square map on the complex-point Thom class

Squaring preserves the original punctured complex plane and therefore
defines a pullback of the original relative singular cochain complex.
Actual unit-circle inclusion and the independent circle square calculation
compute punctured H¹ pullback. Native relative connecting naturality then
computes local relative H² pullback and the ramification factor of the
original Thom class. No projective-line cohomology or Chow map is imported.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ComplexSquareThom

open CategoryTheory HomologicalComplex

abbrev space := ComplexPointThom.space
abbrev punctured := ComplexPointThom.punctured
abbrev Plane := ComplexPointThom.Plane
abbrev puncturedSubcomplex := ComplexPointThom.puncturedSubcomplex

/-- The actual continuous complex polynomial map. -/
def complexSquare : C(ℂ, ℂ) := ⟨fun z ↦ z ^ 2, by fun_prop⟩

def squareMap : space ⟶ space := TopCat.ofHom complexSquare

theorem square_mem_punctured (z : Plane) : (z : ℂ) ^ 2 ∈ punctured := by
  change (z : ℂ) ^ 2 ≠ 0
  exact pow_ne_zero 2 z.property

/-- Squaring on the actual punctured-plane subtype. -/
def puncturedSquare : C(Plane, Plane) :=
  ⟨fun z ↦ ⟨(z : ℂ) ^ 2, square_mem_punctured z⟩,
    (complexSquare.continuous.comp continuous_subtype_val).subtype_mk square_mem_punctured⟩

def puncturedSquareMap : TopCat.of Plane ⟶ TopCat.of Plane :=
  TopCat.ofHom puncturedSquare

@[simp]
theorem puncturedSquareMap_coe (z : Plane) :
    (puncturedSquareMap z : ℂ) = (z : ℂ) ^ 2 := rfl

theorem mapsTo_punctured : Set.MapsTo squareMap punctured punctured := by
  intro z hz
  change z ^ 2 ≠ 0
  exact pow_ne_zero 2 hz

/-- The actual subtype map is bound to the actual ambient square map. -/
theorem puncturedSquareMap_inclusion :
    puncturedSquareMap ≫ SingularSubcomplexes.subsetInclusion space punctured =
      SingularSubcomplexes.subsetInclusion space punctured ≫ squareMap := rfl

/-- The induced map carries every actual punctured simplex to an actual
punctured simplex. -/
theorem pairCondition :
    puncturedSubcomplex ≤ puncturedSubcomplex.preimage (TopCat.toSSet.map squareMap) :=
  RelativeCochains.subsetCondition squareMap punctured punctured mapsTo_punctured

/-- Pullback on the original relative singular cochain kernel. -/
def localRelativePullback :
    RelativeCochains.complex puncturedSubcomplex ⟶
      RelativeCochains.complex puncturedSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map squareMap) pairCondition

/-- Native relative cohomology pullback, induced by the original cochain map. -/
def localPull (n : ℕ) : RelativeCochains.Cohomology puncturedSubcomplex n ⟶
    RelativeCochains.Cohomology puncturedSubcomplex n :=
  homologyMap localRelativePullback n

/-- The actual inclusion of the native unit circle into the punctured plane. -/
def circleInclusion : TopCat.of Circle ⟶ TopCat.of Plane :=
  TopCat.ofHom PuncturedComplexCircle.inclusion

theorem inverseRadial_eq_circleInclusion :
    (TopCat.ofHom PuncturedComplexCircle.homotopyEquiv.invFun :
      TopCat.of Circle ⟶ TopCat.of Plane) = circleInclusion := by
  ext z : 1
  exact PuncturedComplexCircle.homotopyEquiv_symm_apply z

theorem circleInclusion_pullback_injective :
    Function.Injective (SingularCochains.cohomologyPullback circleInclusion 1) := by
  have h : Function.Injective (SingularCochains.cohomologyPullback
      (TopCat.ofHom PuncturedComplexCircle.homotopyEquiv.invFun) 1) :=
    (SingularHomotopy.homotopyEquivIso
      PuncturedComplexCircle.homotopyEquiv 1).symm.toLinearEquiv.injective
  rw [inverseRadial_eq_circleInclusion] at h
  exact h

/-- Squaring commutes with actual unit-circle inclusion, without a radial
normalization calculation. -/
theorem circleInclusion_square :
    circleInclusion ≫ puncturedSquareMap = CircleSquare.squareMap ≫ circleInclusion := by
  ext z : 1
  apply Subtype.ext
  rfl

theorem puncturedPull_square
    (z : SingularCochains.Cohomology (TopCat.of Plane) 1) :
    SingularCochains.cohomologyPullback puncturedSquareMap 1 z = (2 : ℚ) • z := by
  apply circleInclusion_pullback_injective
  have h := congrArg (fun f ↦ SingularCochains.cohomologyPullback f 1) circleInclusion_square
  rw [SingularCochains.cohomologyPullback_comp,
    SingularCochains.cohomologyPullback_comp] at h
  have hz := congrArg (fun f ↦ f z) h
  change SingularCochains.cohomologyPullback circleInclusion 1
      (SingularCochains.cohomologyPullback puncturedSquareMap 1 z) =
    SingularCochains.cohomologyPullback CircleSquare.squareMap 1
      (SingularCochains.cohomologyPullback circleInclusion 1 z) at hz
  rw [CircleSquare.cohomologyPullback_square] at hz
  simpa only [map_smul] using hz

/-- The original relative boundary commutes with the original pair pullback. -/
theorem connecting_square_naturality :
    ComplexPointThom.connecting ≫ localPull 2 =
      SingularCochains.cohomologyPullback puncturedSquareMap 1 ≫
        ComplexPointThom.connecting := by
  simpa only [ComplexPointThom.connecting, ComplexPointThom.puncturedCohomologyIso,
    localPull, localRelativePullback, Category.assoc] using
    RelativeCochains.connecting_subtype_naturality squareMap punctured punctured
      mapsTo_punctured puncturedSquareMap puncturedSquareMap_inclusion 1

/-- The actual local relative H² pullback is independently multiplication
by two, from punctured H¹ and the native relative boundary. -/
theorem localPull_square (z : ComplexPointThom.LocalH2) :
    localPull 2 z = (2 : ℚ) • z := by
  obtain ⟨w, rfl⟩ := ComplexPointThom.connectingIso.toLinearEquiv.surjective z
  have h := congrArg (fun f ↦ f w) connecting_square_naturality
  change localPull 2 (ComplexPointThom.connecting w) =
    ComplexPointThom.connecting
      (SingularCochains.cohomologyPullback puncturedSquareMap 1 w) at h
  rw [puncturedPull_square, map_smul] at h
  exact h

theorem localPull_eq_two_smul_id :
    (localPull 2).hom = (2 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact localPull_square z

/-- The original positively oriented local Thom class retains its actual
ramification weight. -/
theorem localPull_thomClass :
    localPull 2 ComplexPointThom.thomClass = (2 : ℚ) • ComplexPointThom.thomClass :=
  localPull_square _

theorem localPull_thomClass_ne_thomClass :
    localPull 2 ComplexPointThom.thomClass ≠ ComplexPointThom.thomClass := by
  intro h
  have hc := congrArg ComplexPointThom.coordinates h
  rw [localPull_thomClass, map_smul, ComplexPointThom.coordinates_thomClass] at hc
  norm_num at hc

abbrev PointH0 := SingularCochains.Cohomology (TopCat.of ComplexPointThom.Point) 0

theorem square_mem_point (x : ComplexPointThom.Point) : (x : ℂ) ^ 2 ∈ ({0} : Set ℂ) := by
  have hx : (x : ℂ) = 0 := Set.mem_singleton_iff.mp x.property
  rw [hx]
  simp

/-- Restriction of the original square map to its actual singleton zero support. -/
def pointMap : TopCat.of ComplexPointThom.Point ⟶ TopCat.of ComplexPointThom.Point :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x : ℂ) ^ 2, square_mem_point x⟩,
    (complexSquare.continuous.comp continuous_subtype_val).subtype_mk square_mem_point⟩

def pointInclusion : TopCat.of ComplexPointThom.Point ⟶ space :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem pointMap_inclusion : pointMap ≫ pointInclusion = pointInclusion ≫ squareMap := rfl

theorem pointMap_eq_id : pointMap = 𝟙 (TopCat.of ComplexPointThom.Point) := by
  ext x : 1
  exact Subsingleton.elim _ _

def pointPull : PointH0 ⟶ PointH0 := SingularCochains.cohomologyPullback pointMap 0

theorem pointPull_eq_id : pointPull = 𝟙 PointH0 := by
  rw [pointPull, pointMap_eq_id, SingularCochains.cohomologyPullback_id]

@[simp]
theorem pointPull_pointUnit : pointPull ComplexPointThom.pointUnit = ComplexPointThom.pointUnit := by
  simp only [pointPull_eq_id, ModuleCat.id_apply]

/-- The ramified local Gysin square includes the actual factor two; the
reduced point map itself has ordinary unit pullback. -/
theorem localGysin_pullback :
    (localPull 2).hom.comp ComplexPointThom.localGysin =
      (2 : ℚ) • (ComplexPointThom.localGysin.comp pointPull.hom) := by
  apply LinearMap.ext
  intro z
  change localPull 2 (ComplexPointThom.localGysin z) =
    (2 : ℚ) • ComplexPointThom.localGysin (pointPull z)
  simp only [localPull_square, pointPull_eq_id, ModuleCat.id_apply]

end HodgeConjecture.ComplexSquareThom

end
