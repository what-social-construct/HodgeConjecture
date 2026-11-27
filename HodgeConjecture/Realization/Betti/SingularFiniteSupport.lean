module

public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality
public import Mathlib.Topology.Separation.Basic
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Original singular H⁰ on an actual finite support

The source is the original singular cohomology of the actual finite subspace.
Its coordinates are evaluation of the canonical zero-cocycle at actual points.
Singleton restriction is original continuous pullback, and the point delta
classes reconstruct every original class. Empty support has zero source.

These statements use only native cochains and topology, without Chow groups or
a choice of a Gysin map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularFiniteSupport

open CategoryTheory
open scoped BigOperators

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- Coordinates on actual singular H⁰ of any discrete space. -/
def discreteCoordinates (Y : Type v) [TopologicalSpace Y] [DiscreteTopology Y] :
    SingularCochains.Cohomology (TopCat.of Y) 0 ≃ₗ[ℚ] (Y → ℚ) :=
  (SingularCochains.cohomologyZeroIso Y).toLinearEquiv.trans
    (SingularDegreeZero.equivFunctions Y).toLinearEquiv

/-- The coordinate is evaluation on the original actual point simplex. -/
theorem discreteCoordinates_apply (Y : Type v) [TopologicalSpace Y] [DiscreteTopology Y]
    (z : SingularCochains.Cohomology (TopCat.of Y) 0) (p : Y) :
    discreteCoordinates Y z p =
      SingularDegreeZero.eval Y ((SingularCochains.cohomologyZeroIso Y).hom z) p := rfl

theorem discreteCoordinates_pullback {Y : Type u} [TopologicalSpace Y]
    [DiscreteTopology X] [DiscreteTopology Y] (f : C(X, Y))
    (z : SingularCochains.Cohomology (TopCat.of Y) 0) (p : X) :
    discreteCoordinates X (SingularCochains.cohomologyPullback (TopCat.ofHom f) 0 z) p =
      discreteCoordinates Y z (f p) := by
  rw [discreteCoordinates_apply, SingularDegreeZeroNaturality.cohomologyZeroIso_pullback]
  rfl

/-- The original finite subspace, with its original induced topology. -/
abbrev Support (S : Finset X) := ↥(S : Set X)

/-- The original native singular cohomology group, before coordinates. -/
abbrev H0 (S : Finset X) := SingularCochains.Cohomology (TopCat.of (Support S)) 0

/-- The original literal singleton subspace, matching the point Gysin source. -/
abbrev PointSupport (p : X) := ↥({p} : Set X)

abbrev PointH0 (p : X) :=
  SingularCochains.Cohomology (TopCat.of (PointSupport p)) 0

instance pointSupport_unique (p : X) : Unique (PointSupport p) where
  default := ⟨p, rfl⟩
  uniq q := Subtype.ext (Set.mem_singleton_iff.mp q.property)

variable [T1Space X]

instance support_discrete (S : Finset X) : DiscreteTopology (Support S) :=
  Finite.instDiscreteTopology

omit [TopologicalSpace X] [T1Space X] in
theorem support_nonempty_iff (S : Finset X) : Nonempty (Support S) ↔ S.Nonempty := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.val, p.property⟩
  · rintro ⟨p, hp⟩
    exact ⟨⟨p, hp⟩⟩

/-- Actual singular H⁰ is identified with functions on the same actual support. -/
def coordinates (S : Finset X) : H0 S ≃ₗ[ℚ] (Support S → ℚ) :=
  discreteCoordinates (Support S)

theorem coordinates_apply (S : Finset X) (z : H0 S) (p : Support S) :
    coordinates S z p = SingularDegreeZero.eval (Support S)
      ((SingularCochains.cohomologyZeroIso (Support S)).hom z) p := rfl

theorem coordinates_constantClass (S : Finset X) (q : ℚ) (p : Support S) :
    coordinates S (SingularDegreeZeroNaturality.constantClass (Support S) q) p = q := by
  change SingularDegreeZero.eval (Support S)
    ((SingularCochains.cohomologyZeroIso (Support S)).hom
      ((SingularCochains.cohomologyZeroIso (Support S)).inv
        (SingularDegreeZero.constantClass (Support S) q))) p = q
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

local instance : DecidableEq X := Classical.decEq X

/-- The genuine original cohomology class with one point delta coordinates. -/
def deltaClass (S : Finset X) (p : Support S) : H0 S := by
  classical
  exact (coordinates S).symm (fun q ↦ if p = q then 1 else 0)

@[simp]
theorem coordinates_deltaClass (S : Finset X) (p q : Support S) :
    coordinates S (deltaClass S p) q = if p = q then 1 else 0 := by
  classical
  change (coordinates S) ((coordinates S).symm (fun q ↦ if p = q then 1 else 0)) q = _
  exact congrFun ((coordinates S).apply_symm_apply (fun q ↦ if p = q then 1 else 0)) q

theorem deltaClass_ne_zero (S : Finset X) (p : Support S) : deltaClass S p ≠ 0 := by
  intro h
  have hc := coordinates_deltaClass S p p
  rw [h, map_zero] at hc
  norm_num at hc

/-- Point delta classes reconstruct every class of the original singular group. -/
theorem sum_coordinates_deltaClass (S : Finset X) (z : H0 S) :
    (∑ p : Support S, coordinates S z p • deltaClass S p) = z := by
  classical
  apply (coordinates S).injective
  change (coordinates S).toLinearMap (∑ p : Support S,
    coordinates S z p • deltaClass S p) = _
  rw [map_sum]
  ext q
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∑ p : Support S, coordinates S z p * (if p = q then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg (fun t : ℚ ↦ coordinates S z p * t) (coordinates_deltaClass S p q)
    _ = coordinates S z q := by simp [mul_ite]

/-- The original constant class on the literal singleton. -/
def pointUnit (p : X) : PointH0 p :=
  SingularDegreeZeroNaturality.constantClass (PointSupport p) 1

def pointCoordinates (p : X) : PointH0 p ≃ₗ[ℚ] ℚ :=
  (discreteCoordinates (PointSupport p)).trans
    (LinearEquiv.funUnique (PointSupport p) ℚ ℚ)

@[simp]
theorem pointCoordinates_pointUnit (p : X) : pointCoordinates p (pointUnit p) = 1 := by
  change SingularDegreeZero.eval (PointSupport p)
    ((SingularCochains.cohomologyZeroIso (PointSupport p)).hom
      ((SingularCochains.cohomologyZeroIso (PointSupport p)).inv
        (SingularDegreeZero.constantClass (PointSupport p) 1))) default = 1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

theorem point_eq_smul_unit (p : X) (z : PointH0 p) :
    z = pointCoordinates p z • pointUnit p := by
  apply (pointCoordinates p).injective
  rw [map_smul, pointCoordinates_pointUnit, smul_eq_mul, mul_one]

omit [T1Space X] in
/-- The actual inclusion of the literal singleton in the original finite subspace. -/
def singletonInclusion (S : Finset X) (p : Support S) : C(PointSupport p.val, Support S) :=
  ContinuousMap.const _ p

omit [T1Space X] in
/-- Its underlying map is the original inclusion of actual points. -/
theorem singletonInclusion_coe (S : Finset X) (p : Support S) (q : PointSupport p.val) :
    (singletonInclusion S p q : X) = (q : X) :=
  (Set.mem_singleton_iff.mp q.property).symm

omit [T1Space X] in
/-- Original continuous pullback to the literal singleton point Gysin source. -/
def pointRestriction (S : Finset X) (p : Support S) : H0 S →ₗ[ℚ] PointH0 p.val :=
  (SingularCochains.cohomologyPullback (TopCat.ofHom (singletonInclusion S p)) 0).hom

theorem pointCoordinates_pointRestriction (S : Finset X) (p : Support S) (z : H0 S) :
    pointCoordinates p.val (pointRestriction S p z) = coordinates S z p := by
  change discreteCoordinates (PointSupport p.val)
    (SingularCochains.cohomologyPullback (TopCat.ofHom (singletonInclusion S p)) 0 z)
      default = coordinates S z p
  exact discreteCoordinates_pullback (singletonInclusion S p) z default

/-- Singleton restriction is the same original point unit, with its actual coordinate. -/
theorem pointRestriction_eq_coordinate_smul_unit
    (S : Finset X) (p : Support S) (z : H0 S) :
    pointRestriction S p z = coordinates S z p • pointUnit p.val := by
  rw [point_eq_smul_unit p.val (pointRestriction S p z), pointCoordinates_pointRestriction]

@[simp]
theorem pointRestriction_deltaClass (S : Finset X) (p q : Support S) :
    pointRestriction S p (deltaClass S q) = if q = p then pointUnit p.val else 0 := by
  classical
  rw [pointRestriction_eq_coordinate_smul_unit, coordinates_deltaClass]
  split_ifs <;> simp

omit [T1Space X] in
theorem pointRestriction_constantClass (S : Finset X) (p : Support S) (q : ℚ) :
    pointRestriction S p (SingularDegreeZeroNaturality.constantClass (Support S) q) =
      SingularDegreeZeroNaturality.constantClass (PointSupport p.val) q :=
  SingularDegreeZeroNaturality.pullback_constantClass (singletonInclusion S p) q

/-- Sum of the actual point-evaluation coordinates. -/
def sumCoordinates (S : Finset X) : H0 S →ₗ[ℚ] ℚ :=
  (∑ p : Support S, (LinearMap.proj p : (Support S → ℚ) →ₗ[ℚ] ℚ)).comp
    (coordinates S).toLinearMap

theorem sumCoordinates_apply (S : Finset X) (z : H0 S) :
    sumCoordinates S z = ∑ p : Support S, coordinates S z p := by
  simp [sumCoordinates]

/-- The mass of an original constant class is the actual support cardinality times its value. -/
theorem sumCoordinates_constantClass (S : Finset X) (q : ℚ) :
    sumCoordinates S (SingularDegreeZeroNaturality.constantClass (Support S) q) =
      (S.card : ℚ) * q := by
  rw [sumCoordinates_apply]
  calc
    _ = ∑ _p : Support S, q := by
      apply Finset.sum_congr rfl
      intro p hp
      exact coordinates_constantClass S q p
    _ = (S.card : ℚ) * q := by simp

@[simp]
theorem sumCoordinates_deltaClass (S : Finset X) (p : Support S) :
    sumCoordinates S (deltaClass S p) = 1 := by
  classical
  rw [sumCoordinates_apply]
  calc
    _ = ∑ q : Support S, if p = q then (1 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact coordinates_deltaClass S p q
    _ = 1 := by simp

/-- Empty support has zero original singular H⁰; no extra coordinate is introduced. -/
theorem empty_eq_zero (z : H0 (∅ : Finset X)) : z = 0 := by
  apply (coordinates (∅ : Finset X)).injective
  ext p
  exact False.elim (by simpa using p.property)

instance empty_subsingleton : Subsingleton (H0 (∅ : Finset X)) where
  allEq z w := (empty_eq_zero z).trans (empty_eq_zero w).symm

@[simp]
theorem sumCoordinates_empty (z : H0 (∅ : Finset X)) :
    sumCoordinates (∅ : Finset X) z = 0 := by
  rw [empty_eq_zero z, map_zero]

end HodgeConjecture.SingularFiniteSupport

end
