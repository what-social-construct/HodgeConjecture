/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Geometry.AffineComplexPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Topology.EMetricSpace.Paracompact

@[expose] public section

/-!
# Polynomial coordinate spaces of canonical complex points

The original points of `Spec ℂ[Fin d]` have their already constructed
analytic topology. The native presentation-coordinate homeomorphism
identifies them with `Fin d → ℂ`. This reuses the shared affine structure
map and the original section evaluations.

The presentation proof adapts the affine-line argument of AxiomMath/Weil,
revision `27cdb2049be62ee2911429b47f54774078450e32`,
`ComplexPoints/RiemannSurface.lean`, to arbitrary dimension.
Apache-2.0; see `third_party/axiom-weil/LICENSE`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.PolynomialComplexPoints

open AlgebraicGeometry CategoryTheory Topology
open AlgebraicGeometry.Scheme.ComplexPoints

variable (d : ℕ)

/-- The polynomial coordinate model is genuinely smooth of its stated relative dimension. -/
instance smoothOfRelativeDimension :
    SmoothOfRelativeDimension d (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr
  exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)) _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr inferInstance)

/-- The original polynomial variables as global scheme sections. -/
def coordinateSections : Fin d → Γ(Spec (.of (MvPolynomial (Fin d) ℂ)), ⊤) :=
  fun i => (Scheme.ΓSpecIso _).inv (MvPolynomial.X i)

theorem presentationHom_coordinateSections :
    presentationHom (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))
      (coordinateSections d) =
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin d) ℂ))).inv.hom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [presentationHom, MvPolynomial.eval₂Hom_C, constHom,
      AffineComplexPoints.structureMorphism]
    rw [appLE_top_top_eq_appTop, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  · simp [presentationHom, coordinateSections]

theorem zeroLocus_coordinateSections :
    zeroLocus (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))
      (coordinateSections d) = Set.univ := by
  refine Set.eq_univ_of_forall fun z P hP => ?_
  rw [RingHom.mem_ker, presentationHom_coordinateSections] at hP
  have : P = 0 := by
    have h := congrArg (Scheme.ΓSpecIso (.of (MvPolynomial (Fin d) ℂ))).hom.hom hP
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, map_zero] at h
    exact h
  simp [this]

theorem surjective_presentationHom_coordinateSections :
    Function.Surjective (presentationHom
      (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)) (coordinateSections d)) := by
  rw [presentationHom_coordinateSections]
  exact (Scheme.ΓSpecIso (.of (MvPolynomial (Fin d) ℂ))).commRingCatIsoToRingEquiv.symm.surjective

/-- Canonical polynomial scheme points with their independently specified analytic topology. -/
def homeomorph :
    Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)) ≃ₜ (Fin d → ℂ) :=
  (homeomorphZeroLocusOfIsAffine (surjective_presentationHom_coordinateSections d)).trans
    ((Homeomorph.setCongr (zeroLocus_coordinateSections d)).trans (Homeomorph.Set.univ _))

@[simp]
theorem homeomorph_apply
    (p : Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)))
    (i : Fin d) : homeomorph d p i = eval (coordinateSections d i) p (mem_top p) := rfl

/-- The homeomorphism retains each original regular coordinate evaluation. -/
theorem coords_coordinateSections
    (p : Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)))
    (hp : p.Mem ⊤) :
    coords (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))
      (coordinateSections d) ⟨p, hp⟩ = homeomorph d p := rfl

/-- The coordinates of an actual algebra-valued evaluation point are the original tuple. -/
@[simp]
theorem homeomorph_ofAlgHom (z : Fin d → ℂ) :
    homeomorph d (AffineComplexPoints.ofAlgHom (MvPolynomial (Fin d) ℂ) (MvPolynomial.aeval z)) = z := by
  funext i
  rw [homeomorph_apply, AffineComplexPoints.eval_ofAlgHom]
  simp [coordinateSections]

/-- The inverse coordinate map is the original scheme-valued polynomial evaluation point. -/
theorem homeomorph_symm_apply (z : Fin d → ℂ) :
    (homeomorph d).symm z =
      AffineComplexPoints.ofAlgHom (MvPolynomial (Fin d) ℂ) (MvPolynomial.aeval z) := by
  apply (homeomorph d).injective
  rw [Homeomorph.apply_symm_apply, homeomorph_ofAlgHom]

/-- The original canonical topology is Hausdorff, by the proved coordinate homeomorphism. -/
theorem t2Space : T2Space
    (Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))) :=
  (homeomorph d).isEmbedding.t2Space

/-- The same original topology is paracompact in every affine dimension. -/
theorem paracompactSpace : ParacompactSpace
    (Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))) :=
  (homeomorph d).paracompactSpace_iff.mpr inferInstance

/-- Local compactness belongs to the original point topology. -/
theorem locallyCompactSpace : LocallyCompactSpace
    (Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))) :=
  (homeomorph d).isOpenEmbedding.locallyCompactSpace

/-- The same original canonical coordinates give a countable topological basis. -/
theorem secondCountableTopology : SecondCountableTopology
    (Scheme.ComplexPoints (AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ))) :=
  (homeomorph d).isEmbedding.secondCountableTopology

end HodgeConjecture.PolynomialComplexPoints
