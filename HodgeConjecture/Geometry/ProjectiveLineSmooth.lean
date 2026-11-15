module

public import HodgeConjecture.Geometry.ProjectiveLine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

/-!
# Smoothness of the original glued projective line

The same two polynomial charts of the existing scheme are smooth of
relative dimension one. Source locality proves the smoothness of the
original structure morphism, so the canonical analytic atlas applies to
this projective-line model without a supplied smoothness premise.
-/

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory

universe u
variable (k : Type u) [CommRing k]

/-- Either original affine chart is smooth of relative dimension one. -/
instance projectiveLineAffineStructureMorphism_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (projectiveLineAffineStructureMorphism k) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1) (R := k)
      (S := MvPolynomial (Fin 1) k) (MvPolynomial.uniqueAlgEquiv k (Fin 1))
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)) _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance)

/-- Smoothness holds for the actual glued scheme and its original base morphism. -/
instance projectiveLine_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (projectiveLine k ↘ Spec (.of k)) := by
  refine IsZariskiLocalAtSource.of_openCover (projectiveLineOpenCover k) fun i ↦ ?_
  have h : (projectiveLineOpenCover k).f i ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k := (projectiveLineStructureMorphism k).2 i
  rw [h]
  exact projectiveLineAffineStructureMorphism_smoothOfRelativeDimension k

end AlgebraicGeometry
