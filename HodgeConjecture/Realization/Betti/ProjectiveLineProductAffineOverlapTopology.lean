module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineOverlapH2
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover

/-!
# The actual overlap of product affine charts

The intersection of the two affine-first-factor product charts is
homeomorphic to the punctured complex plane times the canonical
projective-line point space.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductAffineOverlapH2

open AlgebraicGeometry CategoryTheory Topology
open HodgeConjecture.ProjectiveLineProductComplexPoints
open HodgeConjecture.ProjectiveLineProductBetti
open HodgeConjecture.ProjectiveLineProductAffineChartH2

/-! ### The original overlap as a product with the punctured complex plane -/

abbrev Plane := PuncturedComplexCircle.Plane

/-- A punctured affine coordinate viewed as a point of the canonical
projective line. -/
def canonicalOverlapPoint (z : Plane) : LinePoint :=
  ProjectiveLineComplexPoints.canonicalHomeomorph
    (ProjectiveLineAnalyticCover.overlapHomeomorph z).val

theorem canonicalOverlapPoint_isEmbedding : IsEmbedding canonicalOverlapPoint :=
  ProjectiveLineComplexPoints.canonicalHomeomorph.isEmbedding.comp
    (IsEmbedding.subtypeVal.comp
      ProjectiveLineAnalyticCover.overlapHomeomorph.isEmbedding)

theorem canonicalOverlapPoint_mem_X (z : Plane) :
    canonicalOverlapPoint z ∈
      Set.range ProjectiveLineComplexPoints.canonicalXChart := by
  obtain ⟨a, ha⟩ := (ProjectiveLineAnalyticCover.overlapHomeomorph z).property.1
  refine ⟨AffineLineComplexPoints.evalPoint a, ?_⟩
  exact congrArg ProjectiveLineComplexPoints.canonicalHomeomorph ha

theorem canonicalOverlapPoint_mem_Y (z : Plane) :
    canonicalOverlapPoint z ∈
      Set.range ProjectiveLineComplexPoints.canonicalYChart := by
  obtain ⟨a, ha⟩ := (ProjectiveLineAnalyticCover.overlapHomeomorph z).property.2
  refine ⟨AffineLineComplexPoints.evalPoint a, ?_⟩
  exact congrArg ProjectiveLineComplexPoints.canonicalHomeomorph ha

/-- Parametrize the actual scheme-product chart intersection by a punctured
first coordinate and an unrestricted second projective-line point. -/
def overlapParam (zp : Plane × LinePoint) : W :=
  ⟨pointsHomeomorph.symm (canonicalOverlapPoint zp.1, zp.2), by
    constructor
    · obtain ⟨a, ha⟩ := canonicalOverlapPoint_mem_X zp.1
      refine ⟨(a, zp.2), ?_⟩
      change pointsHomeomorph.symm
        (ProjectiveLineComplexPoints.canonicalXChart a, zp.2) =
        pointsHomeomorph.symm (canonicalOverlapPoint zp.1, zp.2)
      rw [ha]
    · obtain ⟨a, ha⟩ := canonicalOverlapPoint_mem_Y zp.1
      refine ⟨(a, zp.2), ?_⟩
      change pointsHomeomorph.symm
        (ProjectiveLineComplexPoints.canonicalYChart a, zp.2) =
        pointsHomeomorph.symm (canonicalOverlapPoint zp.1, zp.2)
      rw [ha]⟩

theorem overlapParam_isEmbedding : IsEmbedding overlapParam := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  change IsEmbedding (pointsHomeomorph.symm ∘
    Prod.map canonicalOverlapPoint id)
  exact pointsHomeomorph.symm.isEmbedding.comp
    (canonicalOverlapPoint_isEmbedding.prodMap
      (Homeomorph.refl LinePoint).isEmbedding)

theorem overlapParam_surjective : Function.Surjective overlapParam := by
  intro w
  obtain ⟨⟨a, b⟩, ha⟩ := w.property.1
  obtain ⟨⟨c, d⟩, hc⟩ := w.property.2
  have hX : ProjectiveLineComplexPoints.canonicalXChart a =
      (pointsHomeomorph w.val).1 := by
    have h := congrArg (fun t => (pointsHomeomorph t).1) ha
    simpa [chartMap, firstChart] using h
  have hY : ProjectiveLineComplexPoints.canonicalYChart c =
      (pointsHomeomorph w.val).1 := by
    have h := congrArg (fun t => (pointsHomeomorph t).1) hc
    simpa [chartMap, firstChart] using h
  let q := (pointsHomeomorph w.val).1
  let p : ProjectiveLineComplexPoints.Point :=
    ProjectiveLineComplexPoints.canonicalHomeomorph.symm q
  have hfinite : p ∈ ProjectiveLineAnalyticCover.finiteOpen := by
    refine ⟨a Polynomial.X, ?_⟩
    calc
      ProjectiveLineComplexPoints.finite (a Polynomial.X) =
          ProjectiveLineComplexPoints.xChart a :=
        congrArg ProjectiveLineComplexPoints.xChart
          (AffineLineComplexPoints.evalPoint_coordinate a)
      _ = p := by
        apply ProjectiveLineComplexPoints.canonicalHomeomorph.injective
        change ProjectiveLineComplexPoints.canonicalXChart a =
          ProjectiveLineComplexPoints.canonicalHomeomorph
            (ProjectiveLineComplexPoints.canonicalHomeomorph.symm q)
        rw [Homeomorph.apply_symm_apply]
        exact hX
  have hreciprocal : p ∈ ProjectiveLineAnalyticCover.reciprocalOpen := by
    refine ⟨c Polynomial.X, ?_⟩
    calc
      ProjectiveLineComplexPoints.reciprocal (c Polynomial.X) =
          ProjectiveLineComplexPoints.yChart c :=
        congrArg ProjectiveLineComplexPoints.yChart
          (AffineLineComplexPoints.evalPoint_coordinate c)
      _ = p := by
        apply ProjectiveLineComplexPoints.canonicalHomeomorph.injective
        change ProjectiveLineComplexPoints.canonicalYChart c =
          ProjectiveLineComplexPoints.canonicalHomeomorph
            (ProjectiveLineComplexPoints.canonicalHomeomorph.symm q)
        rw [Homeomorph.apply_symm_apply]
        exact hY
  let z : Plane := ProjectiveLineAnalyticCover.overlapHomeomorph.symm
    ⟨p, hfinite, hreciprocal⟩
  refine ⟨(z, (pointsHomeomorph w.val).2), ?_⟩
  apply Subtype.ext
  apply pointsHomeomorph.injective
  change pointsHomeomorph (pointsHomeomorph.symm
    (canonicalOverlapPoint z, (pointsHomeomorph w.val).2)) = pointsHomeomorph w.val
  rw [Homeomorph.apply_symm_apply]
  apply Prod.ext
  · change ProjectiveLineComplexPoints.canonicalHomeomorph
      (ProjectiveLineAnalyticCover.overlapHomeomorph z).val = q
    rw [show ProjectiveLineAnalyticCover.overlapHomeomorph z =
      (⟨p, ⟨hfinite, hreciprocal⟩⟩ :
        ↥(ProjectiveLineAnalyticCover.finiteOpen ∩
          ProjectiveLineAnalyticCover.reciprocalOpen)) from
      ProjectiveLineAnalyticCover.overlapHomeomorph.apply_symm_apply _]
    exact ProjectiveLineComplexPoints.canonicalHomeomorph.apply_symm_apply q
  · rfl

/-- The actual overlap of the two affine-first-factor charts has the
punctured-plane times projective-line product topology. -/
def overlapHomeomorph : W ≃ₜ Plane × LinePoint :=
  (overlapParam_isEmbedding.toHomeomorphOfSurjective overlapParam_surjective).symm

end HodgeConjecture.ProjectiveLineProductAffineOverlapH2

end
