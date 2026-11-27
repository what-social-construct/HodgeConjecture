module

public import HodgeConjecture.Realization.Betti.Examples.CircleCohomology
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisNaturality

@[expose] public section

/-!
# Actual circle inversion reverses native degree-one cohomology

Inversion fixes both punctures of the original two-chart circle cover.
Its actual overlap map exchanges the two distinguished component points.
Original degree-zero evaluation and original Mayer–Vietoris naturality
therefore prove that native H¹ pullback is negative identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 30000

noncomputable section

namespace HodgeConjecture.CircleInversion

open CategoryTheory CircleTopology

abbrev space : TopCat := TopCat.of Circle

def inversion : C(Circle, Circle) := ⟨Inv.inv, continuous_inv⟩

def inversionMap : space ⟶ space := TopCat.ofHom inversion

@[simp]
theorem inversionMap_apply (z : Circle) : inversionMap z = z⁻¹ := rfl

theorem mapsTo_first : Set.MapsTo inversionMap firstOpen firstOpen := by
  intro z hz h
  apply hz
  change z⁻¹ = -1 at h
  have he := congrArg Inv.inv h
  simpa using he

theorem mapsTo_second : Set.MapsTo inversionMap secondOpen secondOpen := by
  intro z hz h
  apply hz
  change z⁻¹ = 1 at h
  have he := congrArg Inv.inv h
  simpa using he

def overlapMap : TopCat.of overlap ⟶ TopCat.of overlap :=
  SingularMayerVietorisNaturality.intersectionMap inversionMap
    firstOpen secondOpen firstOpen secondOpen mapsTo_first mapsTo_second

@[simp]
theorem overlapMap_coe (z : overlap) : (overlapMap z : Circle) = (z : Circle)⁻¹ := rfl

theorem overlapMap_point (i : Bool) : overlapMap (overlapPoint i) = overlapPoint (!i) := by
  apply Subtype.ext
  cases i
  · change (Circle.exp (-Real.pi / 2))⁻¹ = Circle.exp (Real.pi / 2)
    rw [← Circle.exp_neg]
    congr 1
    ring
  · change (Circle.exp (Real.pi / 2))⁻¹ = Circle.exp (-Real.pi / 2)
    rw [← Circle.exp_neg]
    congr 1
    ring

/-- Actual native overlap H⁰ pullback exchanges the two component evaluations. -/
theorem overlap_coordinates (z : SingularCochains.Cohomology (TopCat.of overlap) 0)
    (i : Bool) :
    CircleCohomology.overlapZeroEquiv
        (SingularCochains.cohomologyPullback overlapMap 0 z) i =
      CircleCohomology.overlapZeroEquiv z (!i) := by
  rw [CircleCohomology.overlapZeroEquiv_apply]
  have h := SingularDegreeZeroNaturality.cohomologyZeroIso_pullback overlapMap.hom z
  change (SingularCochains.cohomologyZeroIso overlap).hom
      (SingularCochains.cohomologyPullback overlapMap 0 z) = _ at h
  rw [h, SingularDegreeZero.eval_pullback]
  change SingularDegreeZero.eval overlap
    ((SingularCochains.cohomologyZeroIso overlap).hom z) (overlapMap (overlapPoint i)) = _
  rw [overlapMap_point]
  rfl

theorem connecting_naturality :
    CircleCohomology.connecting ≫ SingularCochains.cohomologyPullback inversionMap 1 =
      SingularCochains.cohomologyPullback overlapMap 0 ≫ CircleCohomology.connecting :=
  SingularMayerVietorisNaturality.connecting_naturality inversionMap
    firstOpen secondOpen firstOpen secondOpen mapsTo_first mapsTo_second
    firstOpen_isOpen secondOpen_isOpen opens_cover
    firstOpen_isOpen secondOpen_isOpen opens_cover 0

/-- Circle inversion reverses original singular degree-one cohomology. -/
theorem cohomologyPullback_inversion (z : SingularCochains.Cohomology space 1) :
    SingularCochains.cohomologyPullback inversionMap 1 z = -z := by
  obtain ⟨x, rfl⟩ := CircleCohomology.connecting_surjective z
  have h := congrArg (fun f ↦ f x) connecting_naturality
  change SingularCochains.cohomologyPullback inversionMap 1 (CircleCohomology.connecting x) =
    CircleCohomology.connecting (SingularCochains.cohomologyPullback overlapMap 0 x) at h
  apply CircleCohomology.h1Equiv.injective
  rw [h, map_neg, CircleCohomology.h1Equiv_connecting, CircleCohomology.h1Equiv_connecting]
  change CircleCohomology.overlapZeroEquiv
      (SingularCochains.cohomologyPullback overlapMap 0 x) true -
      CircleCohomology.overlapZeroEquiv
        (SingularCochains.cohomologyPullback overlapMap 0 x) false = _
  rw [overlap_coordinates, overlap_coordinates]
  change CircleCohomology.overlapZeroEquiv x false - CircleCohomology.overlapZeroEquiv x true =
    -(CircleCohomology.overlapZeroEquiv x true - CircleCohomology.overlapZeroEquiv x false)
  ring

theorem cohomologyPullback_inversion_eq :
    SingularCochains.cohomologyPullback inversionMap 1 =
      -𝟙 (SingularCochains.Cohomology space 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact cohomologyPullback_inversion z

end HodgeConjecture.CircleInversion

end
