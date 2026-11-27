module

public import HodgeConjecture.Realization.Betti.Examples.CircleInversion
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAffine
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisSwap

@[expose] public section

/-!
# Actual reciprocal chart switch and its positive native H² action

The actual one-point inversion homeomorphism switches the two original
projective-line charts. Circle inversion reverses original overlap H¹,
while interchanging the two cover charts reverses the original boundary.
These two computed signs prove positive identity on original singular H².
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 30000

noncomputable section

namespace HodgeConjecture.ProjectiveLineReciprocal

open CategoryTheory ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

abbrev space : TopCat := TopCat.of Point
abbrev Overlap := ↥(finiteOpen ∩ reciprocalOpen)

/-- Actual compactified complex inversion on the original scheme-point space. -/
def reciprocalHomeomorph : Point ≃ₜ Point :=
  onePointHomeomorph.trans
    (OnePointComplex.inversionHomeomorph.trans onePointHomeomorph.symm)

@[simp]
theorem reciprocalHomeomorph_finite (z : ℂ) :
    reciprocalHomeomorph (finite z) = reciprocal z := by
  change onePointHomeomorph.symm
    (OnePointComplex.inversion (onePointHomeomorph (finite z))) = _
  rw [onePointHomeomorph_finite, onePointHomeomorph_symm_apply,
    fromOnePoint_inversion_coe]

@[simp]
theorem reciprocalHomeomorph_reciprocal (z : ℂ) :
    reciprocalHomeomorph (reciprocal z) = finite z := by
  change onePointHomeomorph.symm
    (OnePointComplex.inversion (onePointHomeomorph (reciprocal z))) = _
  rw [onePointHomeomorph_reciprocal, OnePointComplex.inversion_inversion,
    onePointHomeomorph_symm_apply, fromOnePoint_coe]

def reciprocalContinuousMap : C(Point, Point) :=
  ⟨reciprocalHomeomorph, reciprocalHomeomorph.continuous⟩

def reciprocalMap : space ⟶ space := TopCat.ofHom reciprocalContinuousMap

@[simp]
theorem reciprocalMap_finite (z : ℂ) : reciprocalMap (finite z) = reciprocal z :=
  reciprocalHomeomorph_finite z

@[simp]
theorem reciprocalMap_reciprocal (z : ℂ) : reciprocalMap (reciprocal z) = finite z :=
  reciprocalHomeomorph_reciprocal z

@[simp]
theorem reciprocalMap_zero : reciprocalMap (finite 0) = infinity := reciprocalMap_finite 0

@[simp]
theorem reciprocalMap_infinity : reciprocalMap infinity = finite 0 :=
  reciprocalMap_reciprocal 0

theorem reciprocalMap_involutive : Function.Involutive reciprocalMap := by
  intro p
  rcases finite_or_infinity p with ⟨z, rfl⟩ | rfl
  · rw [reciprocalMap_finite, reciprocalMap_reciprocal]
  · rw [reciprocalMap_infinity, reciprocalMap_finite]
    rfl

theorem mapsTo_finite_reciprocal : Set.MapsTo reciprocalMap finiteOpen reciprocalOpen := by
  rintro _ ⟨z, rfl⟩
  exact ⟨z, (reciprocalMap_finite z).symm⟩

theorem mapsTo_reciprocal_finite : Set.MapsTo reciprocalMap reciprocalOpen finiteOpen := by
  rintro _ ⟨z, rfl⟩
  exact ⟨z, (reciprocalMap_reciprocal z).symm⟩

theorem preimage_reciprocalOpen : reciprocalMap ⁻¹' reciprocalOpen = finiteOpen := by
  ext p
  constructor
  · intro hp
    have h := mapsTo_reciprocal_finite hp
    simpa only [reciprocalMap_involutive p] using h
  · intro hp
    exact mapsTo_finite_reciprocal hp

theorem preimage_finiteOpen : reciprocalMap ⁻¹' finiteOpen = reciprocalOpen := by
  ext p
  constructor
  · intro hp
    have h := mapsTo_finite_reciprocal hp
    simpa only [reciprocalMap_involutive p] using h
  · intro hp
    exact mapsTo_reciprocal_finite hp

/-- The actual overlap map with reversed target-chart order. -/
def swappedOverlapMap : TopCat.of Overlap ⟶ TopCat.of ↥(reciprocalOpen ∩ finiteOpen) :=
  SingularMayerVietorisNaturality.intersectionMap reciprocalMap
    finiteOpen reciprocalOpen reciprocalOpen finiteOpen
    mapsTo_finite_reciprocal mapsTo_reciprocal_finite

/-- The actual reciprocal map of the same original overlap subtype. -/
def overlapMap : TopCat.of Overlap ⟶ TopCat.of Overlap :=
  swappedOverlapMap ≫ SingularMayerVietorisSwap.intersectionSwap space reciprocalOpen finiteOpen

theorem overlapMap_coe (p : Overlap) : (overlapMap p : Point) = reciprocalMap p := rfl

def circleInclusion : TopCat.of Circle ⟶ TopCat.of Overlap :=
  TopCat.ofHom overlapCircleHomotopyEquiv.invFun

theorem circleInclusion_coe (z : Circle) : (circleInclusion z : Point) = finite (z : ℂ) := by
  change (overlapHomeomorph (PuncturedComplexCircle.homotopyEquiv.symm z) : Point) = _
  rw [PuncturedComplexCircle.homotopyEquiv_symm_apply, overlapHomeomorph_coe,
    PuncturedComplexCircle.inclusion_coe]

theorem circleInclusion_pullback_injective :
    Function.Injective (SingularCochains.cohomologyPullback circleInclusion 1) :=
  (SingularHomotopy.homotopyEquivIso overlapCircleHomotopyEquiv 1).symm.toLinearEquiv.injective

theorem circleInclusion_inversion :
    circleInclusion ≫ overlapMap = CircleInversion.inversionMap ≫ circleInclusion := by
  ext z : 1
  apply Subtype.ext
  change (overlapMap (circleInclusion z) : Point) =
    (circleInclusion (CircleInversion.inversionMap z) : Point)
  rw [overlapMap_coe, circleInclusion_coe, reciprocalMap_finite, circleInclusion_coe,
    reciprocal_eq_finite_inv (z : ℂ) z.coe_ne_zero]
  rfl

/-- Actual reciprocal pullback reverses the native overlap H¹ class. -/
theorem overlap_cohomologyPullback (z : SingularCochains.Cohomology (TopCat.of Overlap) 1) :
    SingularCochains.cohomologyPullback overlapMap 1 z = -z := by
  apply circleInclusion_pullback_injective
  have h := congrArg (fun f ↦ SingularCochains.cohomologyPullback f 1) circleInclusion_inversion
  rw [SingularCochains.cohomologyPullback_comp, SingularCochains.cohomologyPullback_comp] at h
  have hz := congrArg (fun f ↦ f z) h
  change SingularCochains.cohomologyPullback circleInclusion 1
      (SingularCochains.cohomologyPullback overlapMap 1 z) =
    SingularCochains.cohomologyPullback CircleInversion.inversionMap 1
      (SingularCochains.cohomologyPullback circleInclusion 1 z) at hz
  rw [CircleInversion.cohomologyPullback_inversion] at hz
  simpa only [map_neg] using hz

theorem reversed_cover : reciprocalOpen ∪ finiteOpen = Set.univ := by
  rw [Set.union_comm]
  exact cover

def reversedConnecting := SingularMayerVietoris.connecting space reciprocalOpen finiteOpen
  isOpen_reciprocalOpen isOpen_finiteOpen reversed_cover 1

/-- The two original sign changes cancel on original singular projective-line H². -/
theorem cohomologyPullback_reciprocal_apply
    (z : SingularCochains.Cohomology space 2) :
    SingularCochains.cohomologyPullback reciprocalMap 2 z = z := by
  obtain ⟨w, rfl⟩ := ProjectiveLineSingularCohomology.connectingIso.toLinearEquiv.surjective z
  let s := SingularMayerVietorisSwap.intersectionSwap space reciprocalOpen finiteOpen
  let v := SingularCochains.cohomologyPullback s 1 w
  have hswap := congrArg (fun f ↦ f w)
    (SingularMayerVietorisSwap.connecting_swap space reciprocalOpen finiteOpen
      isOpen_reciprocalOpen isOpen_finiteOpen reversed_cover 1)
  change reversedConnecting v = -ProjectiveLineSingularCohomology.connecting w at hswap
  have hnat := SingularMayerVietorisNaturality.connecting_naturality reciprocalMap
    finiteOpen reciprocalOpen reciprocalOpen finiteOpen
    mapsTo_finite_reciprocal mapsTo_reciprocal_finite
    isOpen_finiteOpen isOpen_reciprocalOpen cover
    isOpen_reciprocalOpen isOpen_finiteOpen reversed_cover 1
  have hv := congrArg (fun f ↦ f v) hnat
  change SingularCochains.cohomologyPullback reciprocalMap 2 (reversedConnecting v) =
    ProjectiveLineSingularCohomology.connecting
      (SingularCochains.cohomologyPullback swappedOverlapMap 1 v) at hv
  have hoverlap : SingularCochains.cohomologyPullback swappedOverlapMap 1 v = -w := by
    have h := overlap_cohomologyPullback w
    simpa only [overlapMap, SingularCochains.cohomologyPullback_comp, ModuleCat.comp_apply] using h
  rw [hswap, hoverlap, map_neg, map_neg] at hv
  exact neg_injective hv

theorem cohomologyPullback_reciprocal_two :
    SingularCochains.cohomologyPullback reciprocalMap 2 =
      𝟙 (SingularCochains.Cohomology space 2) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact cohomologyPullback_reciprocal_apply z

@[simp]
theorem reciprocalMap_scaled_finite (u : ℂˣ) (z : ℂ) :
    reciprocalMap (ProjectiveLineAffine.affineMap 0 u (finite z)) = reciprocal ((u : ℂ) * z) := by
  rw [ProjectiveLineAffine.affineMap_finite, zero_add, reciprocalMap_finite]

end HodgeConjecture.ProjectiveLineReciprocal

end
