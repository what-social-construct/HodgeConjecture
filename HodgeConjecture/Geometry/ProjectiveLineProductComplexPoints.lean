module

public import HodgeConjecture.Geometry.ProjectiveLineProduct

/-!
# Complex points of the projective-line product

The categorical fiber product represents ordered pairs of complex points of
its factors. This file records the corresponding set equivalence and the
continuity of the projection map for the actual analytic topologies. The
inverse-continuity statement, needed to transport a topological product
cohomology calculation, is a further geometric step.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HodgeConjecture.ProjectiveLineProductComplexPoints

open AlgebraicGeometry

abbrev lineBase := projectiveLine ℂ ↘ Spec (.of ℂ)

abbrev productBase := projectiveLineProductStructureMorphism ℂ

/-- An actual complex point of the product is a pair of complex points of
the two projective-line factors. -/
def pointsEquiv : Scheme.ComplexPoints productBase ≃
    Scheme.ComplexPoints lineBase × Scheme.ComplexPoints lineBase where
  toFun p :=
    ⟨Scheme.ComplexPoints.map (projectiveLineProductFst ℂ)
        (projectiveLineProductFst_comp_structureMorphism ℂ) p,
      Scheme.ComplexPoints.map (projectiveLineProductSnd ℂ)
        (projectiveLineProductSnd_comp_structureMorphism ℂ) p⟩
  invFun pq :=
    ⟨pullback.lift pq.1.hom pq.2.hom (by rw [pq.1.hom_comp, pq.2.hom_comp]), by
      change (pullback.lift pq.1.hom pq.2.hom _ ≫ projectiveLineProductFst ℂ) ≫
        lineBase = 𝟙 _
      rw [pullback.lift_fst]
      exact pq.1.hom_comp⟩
  left_inv p := by
    apply Scheme.ComplexPoints.ext
    apply pullback.hom_ext
    · change pullback.lift (p.hom ≫ projectiveLineProductFst ℂ)
          (p.hom ≫ projectiveLineProductSnd ℂ) _ ≫ projectiveLineProductFst ℂ =
          p.hom ≫ projectiveLineProductFst ℂ
      exact pullback.lift_fst _ _ _
    · change pullback.lift (p.hom ≫ projectiveLineProductFst ℂ)
          (p.hom ≫ projectiveLineProductSnd ℂ) _ ≫ projectiveLineProductSnd ℂ =
          p.hom ≫ projectiveLineProductSnd ℂ
      exact pullback.lift_snd _ _ _
  right_inv pq := by
    apply Prod.ext
    · apply Scheme.ComplexPoints.ext
      change pullback.lift pq.1.hom pq.2.hom _ ≫
          projectiveLineProductFst ℂ = pq.1.hom
      exact pullback.lift_fst _ _ _
    · apply Scheme.ComplexPoints.ext
      change pullback.lift pq.1.hom pq.2.hom _ ≫
          projectiveLineProductSnd ℂ = pq.2.hom
      exact pullback.lift_snd _ _ _

/-- Projection to the pair of factors is continuous for their analytic
topologies. -/
theorem continuous_pointsEquiv : Continuous pointsEquiv :=
  (Scheme.ComplexPoints.continuous_map (projectiveLineProductFst ℂ)
    (projectiveLineProductFst_comp_structureMorphism ℂ)).prodMk
    (Scheme.ComplexPoints.continuous_map (projectiveLineProductSnd ℂ)
      (projectiveLineProductSnd_comp_structureMorphism ℂ))

end HodgeConjecture.ProjectiveLineProductComplexPoints

end
