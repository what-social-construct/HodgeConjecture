module

public import HodgeConjecture.Realization.Betti.RelativeCochains
public import HodgeConjecture.Realization.Betti.Examples.PuncturedComplexCircle
public import HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing
public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.Realization.Betti.SingularMayerVietoris
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-!
# The actual local Thom class of the origin in the complex line

Relative cochains are original simplex functions vanishing on the
punctured-plane singular subcomplex. The original relative connecting
map is an isomorphism from punctured-plane H¹ to local H² because the
ambient complex line is contractible. The local Thom class is its actual
boundary of the actual radial pullback of the positively normalized
circle class. Its positive orientation is fixed by original loop pairing.

The local point Gysin map has the actual singleton's H⁰ as source. Its
value on the original constant unit is this native relative boundary.
No absolute projective-line class or prescribed local dimension is used
to define it. Extension to a global class is a separate excision map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ComplexPointThom

open CategoryTheory CategoryTheory.Limits HomologicalComplex

abbrev space : TopCat := TopCat.of ℂ

/-- The actual open complement of the origin, with its original subtype topology. -/
def punctured : Set ℂ := ({0}ᶜ : Set ℂ)

abbrev Plane := PuncturedComplexCircle.Plane

/-- Original singular simplices contained in that actual punctured open. -/
abbrev puncturedSubcomplex := SingularSubcomplexes.subsetSingular space punctured

/-- Actual local relative cohomology of the pair `(ℂ, ℂ \ {0})`. -/
abbrev LocalH2 := RelativeCochains.Cohomology puncturedSubcomplex 2

/-- The actual contained-simplex comparison with the original punctured-plane subtype. -/
def puncturedCohomologyIso (n : ℕ) :
    (SubcomplexCochains.complex puncturedSubcomplex.toSSet).homology n ≅
      SingularCochains.Cohomology (TopCat.of Plane) n :=
  SingularMayerVietoris.chartCohomologyIso space punctured n

/-- Ambient H¹ vanishing makes the original relative boundary injective. -/
instance nativeConnecting_mono : Mono (RelativeCochains.connecting puncturedSubcomplex 1) := by
  change Mono (RelativeCochains.intersectionSequence puncturedSubcomplex 1).g
  exact (RelativeCochains.intersectionSequence_exact puncturedSubcomplex 1).mono_g
    ((SingularContractible.isZero_cohomology ℂ 1 (by decide)).eq_of_src _ _)

/-- Ambient H² vanishing makes the original relative boundary surjective. -/
instance nativeConnecting_epi : Epi (RelativeCochains.connecting puncturedSubcomplex 1) := by
  change Epi (RelativeCochains.unionSequence puncturedSubcomplex 1).f
  exact (RelativeCochains.unionSequence_exact puncturedSubcomplex 1).epi_f
    ((SingularContractible.isZero_cohomology ℂ 2 (by decide)).eq_of_tgt _ _)

instance nativeConnecting_isIso : IsIso (RelativeCochains.connecting puncturedSubcomplex 1) :=
  isIso_of_mono_of_epi _

/-- The local boundary retains the original punctured subtype and original native relative map. -/
def connecting : SingularCochains.Cohomology (TopCat.of Plane) 1 ⟶ LocalH2 :=
  (puncturedCohomologyIso 1).inv ≫ RelativeCochains.connecting puncturedSubcomplex 1

instance connecting_isIso : IsIso connecting := by
  unfold connecting
  infer_instance

/-- The local boundary itself is the proved local cohomology isomorphism. -/
def connectingIso : SingularCochains.Cohomology (TopCat.of Plane) 1 ≅ LocalH2 := asIso connecting

@[simp]
theorem connectingIso_hom : connectingIso.hom = connecting := rfl

/-- Actual radial pullback followed by the actual native local connecting isomorphism. -/
def circleIso : SingularCochains.Cohomology (TopCat.of Circle) 1 ≅ LocalH2 :=
  SingularHomotopy.homotopyEquivIso PuncturedComplexCircle.homotopyEquiv 1 ≪≫ connectingIso

theorem circleIso_hom : circleIso.hom =
    SingularCochains.cohomologyPullback (TopCat.ofHom PuncturedComplexCircle.radial) 1 ≫
      connecting := rfl

/-- The actual local Thom class is the original boundary of the original positive angular class. -/
def thomClass : LocalH2 := circleIso.hom CircleCohomology.coverGenerator

theorem thomClass_eq_connecting : thomClass =
    connecting (SingularCochains.cohomologyPullback
      (TopCat.ofHom PuncturedComplexCircle.radial) 1 CircleCohomology.coverGenerator) := rfl

/-- The literal native relative boundary formula, before the contained-subtype comparison. -/
theorem thomClass_eq_nativeConnecting : thomClass =
    RelativeCochains.connecting puncturedSubcomplex 1
      ((puncturedCohomologyIso 1).inv
        (SingularCochains.cohomologyPullback (TopCat.ofHom PuncturedComplexCircle.radial) 1
          CircleCohomology.coverGenerator)) := rfl

/-- Local coordinates come from the actual radial and relative-boundary isomorphisms. -/
def coordinates : LocalH2 ≃ₗ[ℚ] ℚ :=
  circleIso.toLinearEquiv.symm.trans CircleCohomology.h1Equiv

theorem coordinates_circleIso (z : SingularCochains.Cohomology (TopCat.of Circle) 1) :
    coordinates (circleIso.hom z) = CircleCohomology.h1Equiv z := by
  change CircleCohomology.h1Equiv
    (circleIso.toLinearEquiv.symm (circleIso.toLinearEquiv z)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp]
theorem coordinates_thomClass : coordinates thomClass = 1 := by
  rw [thomClass, coordinates_circleIso, CircleCohomology.h1Equiv_coverGenerator]

theorem thomClass_ne_zero : thomClass ≠ 0 := by
  intro hz
  have h := coordinates_thomClass
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- The actual inverse local boundary is paired with the actual positive circle cycle. -/
def boundaryPairing : LocalH2 →ₗ[ℚ] ℚ :=
  CircleOrientedPairing.loopPairing.comp circleIso.inv.hom

theorem boundaryPairing_eq_coordinates (z : LocalH2) : boundaryPairing z = coordinates z := by
  change CircleOrientedPairing.loopPairing (circleIso.inv z) = _
  rw [CircleOrientedPairing.loopPairing_eq_coordinate]
  rfl

@[simp]
theorem boundaryPairing_thomClass : boundaryPairing thomClass = 1 := by
  rw [boundaryPairing_eq_coordinates, coordinates_thomClass]

/-- Positive evaluation one uniquely characterizes the actual local orientation class. -/
theorem thomClass_unique (z : LocalH2) (hz : boundaryPairing z = 1) : z = thomClass := by
  apply coordinates.injective
  rw [coordinates_thomClass]
  exact (boundaryPairing_eq_coordinates z).symm.trans hz

theorem eq_smul_thomClass (z : LocalH2) : z = coordinates z • thomClass := by
  apply coordinates.injective
  rw [map_smul, coordinates_thomClass, smul_eq_mul, mul_one]

/-- The nonzero local class forgets to zero in the contractible ambient complex line. -/
theorem forget_thomClass : RelativeCochains.forget puncturedSubcomplex 2 thomClass = 0 :=
  SingularContractible.cohomology_eq_zero ℂ 2 (by decide) _

/-- The rational local orientation map is defined by the actual native local Thom class. -/
def rationalGysin : ℚ →ₗ[ℚ] LocalH2 where
  toFun q := q • thomClass
  map_add' q r := add_smul q r thomClass
  map_smul' q r := by simp [mul_smul]

@[simp]
theorem rationalGysin_one : rationalGysin 1 = thomClass := one_smul ℚ thomClass

@[simp]
theorem coordinates_rationalGysin (q : ℚ) : coordinates (rationalGysin q) = q := by
  change coordinates (q • thomClass) = q
  rw [map_smul, coordinates_thomClass, smul_eq_mul, mul_one]

/-- The original closed origin as an actual singleton subtype space. -/
abbrev Point := ↥({0} : Set ℂ)

def point : Point := ⟨0, rfl⟩

instance point_nonempty : Nonempty Point := ⟨point⟩

instance point_subsingleton : Subsingleton Point where
  allEq x y := Subtype.ext ((Set.mem_singleton_iff.mp x.property).trans
    (Set.mem_singleton_iff.mp y.property).symm)

/-- Original degree-zero point evaluation identifies the actual point's H⁰ with ℚ. -/
def pointCoordinates : SingularCochains.Cohomology (TopCat.of Point) 0 ≃ₗ[ℚ] ℚ :=
  SingularContractible.cohomologyZeroEquiv Point point

/-- The original constant-unit zero-cocycle class on the actual closed point. -/
def pointUnit : SingularCochains.Cohomology (TopCat.of Point) 0 :=
  SingularDegreeZeroNaturality.constantClass Point 1

@[simp]
theorem pointCoordinates_pointUnit : pointCoordinates pointUnit = 1 := by
  change SingularDegreeZero.equivConstants Point point
    ((SingularCochains.cohomologyZeroIso Point).hom
      ((SingularCochains.cohomologyZeroIso Point).inv (SingularDegreeZero.constantClass Point 1))) = 1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

/-- Local point Gysin: actual point H⁰ maps to actual degree-two relative cohomology. -/
def localGysin : SingularCochains.Cohomology (TopCat.of Point) 0 →ₗ[ℚ] LocalH2 :=
  rationalGysin.comp pointCoordinates.toLinearMap

@[simp]
theorem localGysin_pointUnit : localGysin pointUnit = thomClass := by
  change rationalGysin (pointCoordinates pointUnit) = _
  rw [pointCoordinates_pointUnit, rationalGysin_one]

theorem localGysin_eq_smul (z : SingularCochains.Cohomology (TopCat.of Point) 0) :
    localGysin z = pointCoordinates z • thomClass := rfl

/-- The actual oriented point Thom isomorphism, using original point and relative coordinates. -/
def thomIso : SingularCochains.Cohomology (TopCat.of Point) 0 ≃ₗ[ℚ] LocalH2 :=
  pointCoordinates.trans coordinates.symm

theorem thomIso_apply (z : SingularCochains.Cohomology (TopCat.of Point) 0) :
    thomIso z = localGysin z := by
  apply coordinates.injective
  change coordinates (coordinates.symm (pointCoordinates z)) =
    coordinates (rationalGysin (pointCoordinates z))
  rw [LinearEquiv.apply_symm_apply, coordinates_rationalGysin]

theorem localGysin_bijective : Function.Bijective localGysin := by
  have h : (localGysin : SingularCochains.Cohomology (TopCat.of Point) 0 → LocalH2) = thomIso :=
    funext (fun z ↦ (thomIso_apply z).symm)
  rw [h]
  exact thomIso.bijective

end HodgeConjecture.ComplexPointThom
