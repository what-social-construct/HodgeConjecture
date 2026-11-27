module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAffine
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLinePointSupport
public import HodgeConjecture.Realization.Betti.Examples.ComplexPointThom

@[expose] public section

/-!
# Actual singleton supports at arbitrary finite projective-line points

The support and its complement are original subspaces of the original
complex scheme-point space. Translation identifies the complement with
the original reciprocal chart. The support retains its original native
degree-zero cohomology and constant unit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFinitePointSupport

open CategoryTheory ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

def support (a : ℂ) : Set Point := {finite a}

def complement (a : ℂ) : Set Point := (support a)ᶜ

theorem complement_isOpen (a : ℂ) : IsOpen (complement a) :=
  isClosed_singleton.isOpen_compl

@[simp]
theorem mem_complement_iff (a : ℂ) (p : Point) : p ∈ complement a ↔ p ≠ finite a := Iff.rfl

@[simp]
theorem finite_mem_complement_iff (a z : ℂ) : finite z ∈ complement a ↔ z ≠ a :=
  not_congr finite_injective.eq_iff

@[simp]
theorem infinity_mem_complement (a : ℂ) : infinity ∈ complement a :=
  (finite_ne_infinity a).symm

/-- The original finite chart and the actual complement cover the point space. -/
theorem cover (a : ℂ) : finiteOpen ∪ complement a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  by_cases hp : p = finite a
  · subst p
    exact Or.inl ⟨a, rfl⟩
  · exact Or.inr hp

/-- The actual affine map takes precisely the original zero complement to the moved complement. -/
theorem preimage_complement (a : ℂ) (u : ℂˣ) :
    ProjectiveLineAffine.affineMap a u ⁻¹' complement a = reciprocalOpen := by
  rw [ProjectiveLinePointSupport.reciprocalOpen_eq_puncturedOpen]
  ext p
  change ProjectiveLineAffine.affineHomeomorph a u p ≠ finite a ↔ p ≠ finite 0
  have hzero : ProjectiveLineAffine.affineHomeomorph a u (finite 0) = finite a := by simp
  rw [← hzero]
  exact not_congr (ProjectiveLineAffine.affineHomeomorph a u).injective.eq_iff

theorem mapsTo_complement (a : ℂ) (u : ℂˣ) :
    Set.MapsTo (ProjectiveLineAffine.affineMap a u) reciprocalOpen (complement a) := by
  intro p hp
  change p ∈ ProjectiveLineAffine.affineMap a u ⁻¹' complement a
  rw [preimage_complement]
  exact hp

private theorem translation_inverse_mem (a : ℂ) (p : Point) :
    p ∈ complement a ↔
      (ProjectiveLineAffine.affineHomeomorph a 1).symm p ∈
        ProjectiveLinePointSupport.puncturedOpen := by
  change p ≠ finite a ↔ (ProjectiveLineAffine.affineHomeomorph a 1).symm p ≠ finite 0
  apply not_congr
  constructor
  · intro hp
    rw [hp]
    apply (ProjectiveLineAffine.affineHomeomorph a 1).injective
    simp
  · intro hp
    have h := congrArg (ProjectiveLineAffine.affineHomeomorph a 1) hp
    simpa using h

/-- Actual translation identifies the moved complement with the original reciprocal chart. -/
def complementHomeomorph (a : ℂ) : ↥(complement a) ≃ₜ ↥reciprocalOpen :=
  ((ProjectiveLineAffine.affineHomeomorph a 1).symm.subtype
    (translation_inverse_mem a)).trans
      (Homeomorph.setCongr ProjectiveLinePointSupport.reciprocalOpen_eq_puncturedOpen.symm)

@[simp]
theorem complementHomeomorph_coe (a : ℂ) (p : ↥(complement a)) :
    (complementHomeomorph a p : Point) =
      (ProjectiveLineAffine.affineHomeomorph a 1).symm p := rfl

instance complementContractibleSpace (a : ℂ) : ContractibleSpace ↥(complement a) :=
  (complementHomeomorph a).symm.contractibleSpace

abbrev PointSupport (a : ℂ) := ↥(support a)

def point (a : ℂ) : PointSupport a := ⟨finite a, rfl⟩

instance pointSupport_nonempty (a : ℂ) : Nonempty (PointSupport a) := ⟨point a⟩

instance pointSupport_subsingleton (a : ℂ) : Subsingleton (PointSupport a) where
  allEq x y := Subtype.ext ((Set.mem_singleton_iff.mp x.property).trans
    (Set.mem_singleton_iff.mp y.property).symm)

/-- The actual zero of the normal complex coordinate maps to the actual finite support. -/
def pointNormalHomeomorph (a : ℂ) : ComplexPointThom.Point ≃ₜ PointSupport a where
  toFun _ := point a
  invFun _ := ComplexPointThom.point
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

@[simp]
theorem pointNormalHomeomorph_coe (a : ℂ) (x : ComplexPointThom.Point) :
    (pointNormalHomeomorph a x : Point) = finite a := rfl

/-- The singleton map agrees with the literal translated finite normal coordinate. -/
theorem pointNormalHomeomorph_finite (a : ℂ) (x : ComplexPointThom.Point) :
    (pointNormalHomeomorph a x : Point) = finite (a + x.val) := by
  rw [Set.mem_singleton_iff.mp x.property, add_zero]
  rfl

abbrev PointH0 (a : ℂ) := SingularCochains.Cohomology (TopCat.of (PointSupport a)) 0

/-- Native point evaluation on the original singleton's degree-zero cohomology. -/
def pointCoordinates (a : ℂ) : PointH0 a ≃ₗ[ℚ] ℚ :=
  SingularContractible.cohomologyZeroEquiv (PointSupport a) (point a)

/-- The original constant one class on the actual finite support. -/
def pointUnit (a : ℂ) : PointH0 a :=
  SingularDegreeZeroNaturality.constantClass (PointSupport a) 1

@[simp]
theorem pointCoordinates_pointUnit (a : ℂ) : pointCoordinates a (pointUnit a) = 1 := by
  change SingularDegreeZero.equivConstants (PointSupport a) (point a)
    ((SingularCochains.cohomologyZeroIso (PointSupport a)).hom
      ((SingularCochains.cohomologyZeroIso (PointSupport a)).inv
        (SingularDegreeZero.constantClass (PointSupport a) 1))) = 1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

end HodgeConjecture.ProjectiveLineFinitePointSupport
