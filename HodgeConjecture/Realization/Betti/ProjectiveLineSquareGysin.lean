module

public import HodgeConjecture.Realization.Betti.ProjectiveLineSquarePullback
public import HodgeConjecture.Realization.Betti.ProjectiveLinePointGysin
public import HodgeConjecture.Realization.Transfer

@[expose] public section

/-!
# A zero-supported point-Gysin trace for the projective-line square map

The actual square map fixes the actual singleton zero support. Its induced
map on that support is a homeomorphism, so inverse native H⁰ pullback is
the support transfer. The existing geometric zero-point Gysin isomorphism
transports it to native H². This construction is independent of Chow groups
and of cohomology coordinates. It is a degree-specific supported trace;
no general branched trace or arbitrary point-Gysin naturality is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquareGysin

open CategoryTheory ProjectiveLineComplexPoints ProjectiveLinePointSupport

abbrev PointH0 := ProjectiveLinePointGysin.PointH0
abbrev Betti := ProjectiveLinePointGysin.AbsoluteH2

theorem pointMap_mem_support (x : PointSupport) :
    ProjectiveLineSquarePullback.pointMap x.val ∈ support := by
  have hx : x.val = zeroPoint := Set.mem_singleton_iff.mp x.property
  change ProjectiveLineSquarePullback.pointMap x.val = zeroPoint
  rw [hx]
  exact ProjectiveLineSquarePullback.pointMap_zero

/-- The restriction of the original geometric square map to its actual fixed support. -/
def supportMap : TopCat.of PointSupport ⟶ TopCat.of PointSupport :=
  TopCat.ofHom ⟨fun x ↦ ⟨ProjectiveLineSquarePullback.pointMap x.val, pointMap_mem_support x⟩,
    (ProjectiveLineSquarePullback.pointMap.hom.continuous.comp
      continuous_subtype_val).subtype_mk pointMap_mem_support⟩

/-- The support map is bound to the original absolute map by actual inclusion. -/
theorem supportMap_inclusion :
    supportMap ≫ SingularSubcomplexes.subsetInclusion
        (TopCat.of Point) support =
      SingularSubcomplexes.subsetInclusion (TopCat.of Point) support ≫
        ProjectiveLineSquarePullback.pointMap := rfl

theorem supportMap_eq_id : supportMap = 𝟙 (TopCat.of PointSupport) := by
  ext x : 1
  exact Subsingleton.elim _ _

/-- The actual support bijection, retaining its original forward map. -/
def supportHomeomorph : PointSupport ≃ₜ PointSupport where
  toFun := supportMap
  invFun := id
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := supportMap.hom.continuous
  continuous_invFun := continuous_id

def supportPullbackIso : PointH0 ≅ PointH0 :=
  SingularHomotopy.homeomorphIso supportHomeomorph 0

theorem supportPullbackIso_hom :
    supportPullbackIso.hom = SingularCochains.cohomologyPullback supportMap 0 := rfl

/-- Transfer along the actual singleton bijection is inverse native pullback. -/
def pointPush : PointH0 →ₗ[ℚ] PointH0 := supportPullbackIso.inv.hom

theorem pointPush_eq_id : pointPush = LinearMap.id := by
  have h : supportPullbackIso.hom = 𝟙 PointH0 := by
    rw [supportPullbackIso_hom, supportMap_eq_id, SingularCochains.cohomologyPullback_id]
  have hi : supportPullbackIso.inv = 𝟙 PointH0 := by
    simpa only [h, Category.comp_id] using supportPullbackIso.inv_hom_id
  change supportPullbackIso.inv.hom = LinearMap.id
  rw [hi]
  rfl

abbrev gysinComparison := ProjectiveLinePointGysin.gysinIso.toLinearEquiv

/-- The actual zero-point Gysin construction transports the support transfer to H². -/
def push : Betti →ₗ[ℚ] Betti :=
  gysinComparison.toLinearMap.comp (pointPush.comp gysinComparison.symm.toLinearMap)

theorem push_gysin (z : PointH0) :
    push (ProjectiveLinePointGysin.gysin z) =
      ProjectiveLinePointGysin.gysin (pointPush z) := by
  have hz : ProjectiveLinePointGysin.gysin z = gysinComparison z :=
    (ProjectiveLinePointGysin.gysinIso_apply z).symm
  change gysinComparison
    (pointPush (gysinComparison.symm (ProjectiveLinePointGysin.gysin z))) = _
  rw [hz, gysinComparison.symm_apply_apply]
  exact ProjectiveLinePointGysin.gysinIso_apply (pointPush z)

/-- This particular degree-specific geometric trace is identity, as proved after construction. -/
theorem push_eq_id : push = LinearMap.id := by
  apply LinearMap.ext
  intro z
  change gysinComparison (pointPush (gysinComparison.symm z)) = z
  rw [pointPush_eq_id, LinearMap.id_apply]
  exact gysinComparison.apply_symm_apply z

/-- Positive degree comes from the independently computed actual native pullback. -/
def degreeTransfer : RationalDegreeTransfer Betti Betti where
  pull := (SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2).hom
  push := push
  degree := 2
  degree_ne_zero := by decide
  push_comp_pull := by
    rw [push_eq_id, LinearMap.id_comp]
    exact ProjectiveLineSquarePullback.cohomologyPullback_square_eq

end HodgeConjecture.ProjectiveLineSquareGysin

end
