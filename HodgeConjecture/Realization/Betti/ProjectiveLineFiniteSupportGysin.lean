module

public import HodgeConjecture.Realization.Betti.ProjectiveLineSupportedPoint
public import HodgeConjecture.Realization.Betti.SingularSupports

@[expose] public section

/-!
# Original geometric Gysin for an actual finite support

Original singleton restrictions on native H⁰, actual point Thom/excision
isomorphisms and the proved sum of original support extensions define the map.
Its supported isomorphism uses finite relative decomposition. Forgetting is
the sum of the actual point coordinates and need not be injective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFiniteSupportGysin

open CategoryTheory
open ProjectiveLineComplexPoints
open scoped BigOperators

abbrev Support (S : Finset Point) := SingularFiniteSupport.Support S
abbrev H0 (S : Finset Point) := SingularFiniteSupport.H0 S
abbrev SupportedH2 (S : Finset Point) := SingularSupports.Supported Point (S : Set Point) 2
abbrev AbsoluteH2 := ProjectiveLinePointGysin.AbsoluteH2

/-- This equivalence has the original singleton restrictions as its actual components. -/
def pointRestrictionsEquiv (S : Finset Point) :
    H0 S ≃ₗ[ℚ] ((p : Support S) → ProjectiveLineSupportedPoint.PointH0 p.val) :=
  (SingularFiniteSupport.coordinates S).trans
    (LinearEquiv.piCongrRight (fun p : Support S ↦
      SingularFiniteSupport.pointCoordinates p.val)).symm

theorem pointRestrictionsEquiv_apply (S : Finset Point) (z : H0 S) (p : Support S) :
    pointRestrictionsEquiv S z p = SingularFiniteSupport.pointRestriction S p z := by
  apply (SingularFiniteSupport.pointCoordinates p.val).injective
  change SingularFiniteSupport.pointCoordinates p.val
    ((SingularFiniteSupport.pointCoordinates p.val).symm
      (SingularFiniteSupport.coordinates S z p)) = _
  rw [LinearEquiv.apply_symm_apply, SingularFiniteSupport.pointCoordinates_pointRestriction]

/-- The original finite family of local point Thom maps, after actual singleton restriction. -/
def componentMap (S : Finset Point) : H0 S →ₗ[ℚ] SingularSupports.Family Point S 2 :=
  LinearMap.pi (fun p : Support S ↦
    (ProjectiveLineSupportedPoint.supportedGysin p.val).comp
      (SingularFiniteSupport.pointRestriction S p))

def supportedGysin (S : Finset Point) : H0 S →ₗ[ℚ] SupportedH2 S :=
  (SingularSupports.assemble Point S 2).comp (componentMap S)

/-- Original inclusion of the actual finite-support relative cochains. -/
def gysin (S : Finset Point) : H0 S →ₗ[ℚ] AbsoluteH2 :=
  (SingularSupports.forget Point (S : Set Point) 2).comp (supportedGysin S)

def gysinEquiv (S : Finset Point) : H0 S ≃ₗ[ℚ] SupportedH2 S :=
  (pointRestrictionsEquiv S).trans
    ((LinearEquiv.piCongrRight (fun p : Support S ↦
      (ProjectiveLineSupportedPoint.gysinIso p.val).toLinearEquiv)).trans
        (SingularSupports.assembleEquiv Point S 2))

theorem gysinEquiv_apply (S : Finset Point) (z : H0 S) :
    gysinEquiv S z = supportedGysin S z := by
  change SingularSupports.assemble Point S 2
    (fun p ↦ ProjectiveLineSupportedPoint.supportedGysin p.val (pointRestrictionsEquiv S z p)) =
      SingularSupports.assemble Point S 2
        (fun p ↦ ProjectiveLineSupportedPoint.supportedGysin p.val
          (SingularFiniteSupport.pointRestriction S p z))
  congr 1
  funext p
  rw [pointRestrictionsEquiv_apply]

/-- This injectivity comes from native relative decomposition, never from absolute forgetting. -/
theorem supportedGysin_bijective (S : Finset Point) : Function.Bijective (supportedGysin S) := by
  have h : (supportedGysin S : H0 S → SupportedH2 S) = gysinEquiv S :=
    funext (fun z ↦ (gysinEquiv_apply S z).symm)
  rw [h]
  exact (gysinEquiv S).bijective

theorem gysin_apply (S : Finset Point) (z : H0 S) :
    gysin S z = SingularFiniteSupport.sumCoordinates S z •
      ProjectiveLineBettiCohomology.coverGenerator := by
  change SingularSupports.forget Point (S : Set Point) 2
    (SingularSupports.assemble Point S 2
      (fun p ↦ ProjectiveLineSupportedPoint.supportedGysin p.val
        (SingularFiniteSupport.pointRestriction S p z))) = _
  rw [SingularSupports.forget_assemble]
  change (∑ p : Support S, ProjectiveLineSupportedPoint.gysin p.val
    (SingularFiniteSupport.pointRestriction S p z)) = _
  simp_rw [ProjectiveLineSupportedPoint.gysin_apply,
    SingularFiniteSupport.pointCoordinates_pointRestriction]
  rw [← Finset.sum_smul, SingularFiniteSupport.sumCoordinates_apply]

theorem supportedGysin_deltaClass (S : Finset Point) (p : Support S) :
    supportedGysin S (SingularFiniteSupport.deltaClass S p) =
      SingularSupports.singletonExtension Point S p 2
        (ProjectiveLineSupportedPoint.supportedGysin p.val
          (SingularFiniteSupport.pointUnit p.val)) := by
  classical
  change SingularSupports.assemble Point S 2
    (componentMap S (SingularFiniteSupport.deltaClass S p)) = _
  rw [SingularSupports.assemble_apply]
  refine (Finset.sum_eq_single p ?_ ?_).trans ?_
  · intro q _ hqp
    change SingularSupports.singletonExtension Point S q 2
      (ProjectiveLineSupportedPoint.supportedGysin q.val
        (SingularFiniteSupport.pointRestriction S q (SingularFiniteSupport.deltaClass S p))) = 0
    rw [SingularFiniteSupport.pointRestriction_deltaClass, ite_eq_right (Ne.symm hqp),
      map_zero, map_zero]
  · intro hp
    simp at hp
  · change SingularSupports.singletonExtension Point S p 2
      (ProjectiveLineSupportedPoint.supportedGysin p.val
        (SingularFiniteSupport.pointRestriction S p (SingularFiniteSupport.deltaClass S p))) = _
    rw [SingularFiniteSupport.pointRestriction_deltaClass, ite_eq_left rfl]

@[simp]
theorem gysin_deltaClass (S : Finset Point) (p : Support S) :
    gysin S (SingularFiniteSupport.deltaClass S p) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [gysin_apply, SingularFiniteSupport.sumCoordinates_deltaClass, one_smul]

theorem delta_difference_ne_zero (S : Finset Point) (p q : Support S) (hpq : p ≠ q) :
    SingularFiniteSupport.deltaClass S p - SingularFiniteSupport.deltaClass S q ≠ 0 := by
  classical
  intro h
  have hc := congrArg (fun z ↦ SingularFiniteSupport.coordinates S z p) (sub_eq_zero.mp h)
  rw [SingularFiniteSupport.coordinates_deltaClass, SingularFiniteSupport.coordinates_deltaClass,
    ite_eq_left rfl, ite_eq_right (Ne.symm hpq)] at hc
  exact one_ne_zero hc

/-- Distinct point contributions remain distinct in the original supported target. -/
theorem supported_difference_ne_zero (S : Finset Point) (p q : Support S) (hpq : p ≠ q) :
    supportedGysin S (SingularFiniteSupport.deltaClass S p -
      SingularFiniteSupport.deltaClass S q) ≠ 0 := by
  intro h
  apply delta_difference_ne_zero S p q hpq
  apply (supportedGysin_bijective S).injective
  simpa only [map_zero] using h

/-- Their balanced difference has zero absolute class; faithful forgetting cannot be assumed. -/
theorem forget_difference_zero (S : Finset Point) (p q : Support S) :
    SingularSupports.forget Point (S : Set Point) 2
      (supportedGysin S (SingularFiniteSupport.deltaClass S p -
        SingularFiniteSupport.deltaClass S q)) = 0 := by
  change gysin S (SingularFiniteSupport.deltaClass S p -
    SingularFiniteSupport.deltaClass S q) = 0
  rw [map_sub, gysin_deltaClass, gysin_deltaClass, sub_self]

theorem forget_not_injective (S : Finset Point) (p q : Support S) (hpq : p ≠ q) :
    ¬ Function.Injective (SingularSupports.forget Point (S : Set Point) 2) := by
  intro h
  apply supported_difference_ne_zero S p q hpq
  apply h
  simpa only [map_zero] using forget_difference_zero S p q

theorem empty_supportedGysin (z : H0 (∅ : Finset Point)) : supportedGysin ∅ z = 0 := by
  rw [SingularFiniteSupport.empty_eq_zero z, map_zero]

theorem empty_gysin (z : H0 (∅ : Finset Point)) : gysin ∅ z = 0 := by
  rw [SingularFiniteSupport.empty_eq_zero z, map_zero]

end HodgeConjecture.ProjectiveLineFiniteSupportGysin

end
