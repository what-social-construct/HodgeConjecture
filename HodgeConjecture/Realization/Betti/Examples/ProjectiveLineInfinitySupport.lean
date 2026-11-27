module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover
public import HodgeConjecture.Realization.Betti.Examples.ComplexPointThom

@[expose] public section

/-! The original singleton at infinity, its actual finite-chart complement,
and its native degree-zero cohomology. No cycle class chooses these data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineInfinitySupport

open AlgebraicGeometry CategoryTheory ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

def support : Set Point := {infinity}

abbrev complement : Set Point := finiteOpen

theorem complement_eq : complement = supportᶜ := range_finite

theorem complement_isOpen : IsOpen complement := isOpen_finiteOpen

theorem cover : reciprocalOpen ∪ complement = Set.univ := by
  rw [Set.union_comm]
  exact ProjectiveLineAnalyticCover.cover

@[simp]
theorem reciprocal_mem_complement_iff (z : ℂ) : reciprocal z ∈ complement ↔ z ≠ 0 := by
  rw [complement_eq]
  change reciprocal z ≠ reciprocal 0 ↔ z ≠ 0
  exact not_congr isOpenEmbedding_reciprocal.injective.eq_iff

abbrev PointSupport := ↥support

def point : PointSupport := ⟨infinity, rfl⟩

instance pointSupport_nonempty : Nonempty PointSupport := ⟨point⟩

instance pointSupport_subsingleton : Subsingleton PointSupport where
  allEq x y := Subtype.ext ((Set.mem_singleton_iff.mp x.property).trans
    (Set.mem_singleton_iff.mp y.property).symm)

def pointNormalHomeomorph : ComplexPointThom.Point ≃ₜ PointSupport where
  toFun _ := point
  invFun _ := ComplexPointThom.point
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

@[simp]
theorem pointNormalHomeomorph_coe (x : ComplexPointThom.Point) :
    (pointNormalHomeomorph x : Point) = infinity := rfl

theorem pointSupport_scheme_base (p : PointSupport) (q : Spec (.of ℂ)) :
    schemeMorphism p.val q = projectiveLineInfinity ℂ := by
  have hp : p.val = infinity := Set.mem_singleton_iff.mp p.property
  rw [hp]
  exact infinity_base q

abbrev PointH0 := SingularCochains.Cohomology (TopCat.of PointSupport) 0

def pointCoordinates : PointH0 ≃ₗ[ℚ] ℚ :=
  SingularContractible.cohomologyZeroEquiv PointSupport point

def pointUnit : PointH0 := SingularDegreeZeroNaturality.constantClass PointSupport 1

@[simp]
theorem pointCoordinates_pointUnit : pointCoordinates pointUnit = 1 := by
  change SingularDegreeZero.equivConstants PointSupport point
    ((SingularCochains.cohomologyZeroIso PointSupport).hom
      ((SingularCochains.cohomologyZeroIso PointSupport).inv
        (SingularDegreeZero.constantClass PointSupport 1))) = 1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

end HodgeConjecture.ProjectiveLineInfinitySupport

end
