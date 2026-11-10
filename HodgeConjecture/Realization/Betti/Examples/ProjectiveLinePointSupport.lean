module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover
public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality
public import HodgeConjecture.Realization.Betti.SingularContractible

@[expose] public section

/-!
# The actual projective-line zero point and its complement

The original reciprocal chart is exactly the complement of the actual
finite zero point. The finite complex chart sends its original zero to
the original scheme point `projectiveLineZero`. The singleton support
retains its actual topology, point H⁰ and original constant-unit class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLinePointSupport

open CategoryTheory AlgebraicGeometry ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

def zeroPoint : Point := finite 0

def support : Set Point := {zeroPoint}

def puncturedOpen : Set Point := supportᶜ

/-- The original reciprocal chart is the actual complement of the original zero point. -/
theorem reciprocalOpen_eq_puncturedOpen : reciprocalOpen = puncturedOpen := by
  ext p
  rcases finite_or_infinity p with ⟨z, rfl⟩ | rfl
  · rw [finite_mem_reciprocal_iff]
    change z ≠ 0 ↔ finite z ≠ finite 0
    exact not_congr finite_injective.eq_iff.symm
  · constructor
    · intro _
      change infinity ≠ finite 0
      exact (finite_ne_infinity 0).symm
    · intro _
      exact ⟨0, rfl⟩

theorem puncturedOpen_isOpen : IsOpen puncturedOpen := by
  rw [← reciprocalOpen_eq_puncturedOpen]
  exact isOpen_reciprocalOpen

/-- The original finite complex point at zero has exactly the original scheme zero as image. -/
theorem zeroPoint_scheme_base (q : Spec (.of ℂ)) :
    schemeMorphism zeroPoint q = projectiveLineZero ℂ := by
  change projectiveLineXChart ℂ (affineMorphism (AffineLineComplexPoints.evalPoint 0) q) = _
  rw [affine_zero_base]
  rfl

/-- The original scheme zero supports an actual closed-point cycle, rather than the generic point. -/
theorem schemeZero_ne_genericPoint :
    projectiveLineZero ℂ ≠ genericPoint (projectiveLine ℂ) := by
  intro h
  have he : (projectiveLineXChart ℂ).base (affineLineOrigin ℂ) =
      (projectiveLineXChart ℂ).base (genericPoint (Spec (.of (Polynomial ℂ)))) :=
    h.trans (projectiveLineXChart_genericPoint_eq (k := ℂ)).symm
  have hp := projectiveLineXChart_base_injective he
  have hx : (Polynomial.X : Polynomial ℂ) ∈
      (genericPoint (Spec (.of (Polynomial ℂ)))).asIdeal := by
    rw [← hp]
    exact Ideal.subset_span rfl
  rw [genericPoint_eq_bot_of_affine] at hx
  exact Polynomial.X_ne_zero hx

abbrev PointSupport := ↥support

def point : PointSupport := ⟨zeroPoint, rfl⟩

instance pointSupport_nonempty : Nonempty PointSupport := ⟨point⟩

instance pointSupport_subsingleton : Subsingleton PointSupport where
  allEq x y := Subtype.ext ((Set.mem_singleton_iff.mp x.property).trans
    (Set.mem_singleton_iff.mp y.property).symm)

/-- The actual normal-coordinate singleton maps to the actual projective-line support. -/
def pointHomeomorph : ↥({0} : Set ℂ) ≃ₜ PointSupport where
  toFun _ := point
  invFun _ := ⟨0, rfl⟩
  left_inv x := Subtype.ext (Set.mem_singleton_iff.mp x.property).symm
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The support map agrees with the original finite coordinate chart. -/
theorem pointHomeomorph_coe (x : ↥({0} : Set ℂ)) :
    (pointHomeomorph x : Point) = finite x.val := by
  rw [Set.mem_singleton_iff.mp x.property]
  rfl

def pointCoordinates : SingularCochains.Cohomology (TopCat.of PointSupport) 0 ≃ₗ[ℚ] ℚ :=
  SingularContractible.cohomologyZeroEquiv PointSupport point

/-- The original constant one class on the actual projective-line support. -/
def pointUnit : SingularCochains.Cohomology (TopCat.of PointSupport) 0 :=
  SingularDegreeZeroNaturality.constantClass PointSupport 1

@[simp]
theorem pointCoordinates_pointUnit : pointCoordinates pointUnit = 1 := by
  change SingularDegreeZero.equivConstants PointSupport point
    ((SingularCochains.cohomologyZeroIso PointSupport).hom
      ((SingularCochains.cohomologyZeroIso PointSupport).inv
        (SingularDegreeZero.constantClass PointSupport 1))) = 1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

end HodgeConjecture.ProjectiveLinePointSupport
