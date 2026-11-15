module

public import HodgeConjecture.Geometry.AffineComplexPoints
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Complex points of an affine product

The evaluation topology on complex-algebra points of `A ⊗[ℂ] B` agrees
with the product of the evaluation topologies on points of `A` and `B`.
The homeomorphism restricts an algebra map to the two tensor factors;
its inverse is the algebra tensor-product universal map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.AffineComplexPointsProduct

open Algebra.TensorProduct TensorProduct

variable (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

attribute [local instance] AffineComplexPoints.evaluationTopology

/-- Algebra-valued complex points of the tensor product correspond to
pairs of algebra-valued points of its factors. -/
def pointEquiv :
    (AffineComplexPoints.algebraPointSpace (A ⊗[ℂ] B)) ≃
      ((AffineComplexPoints.algebraPointSpace A) ×
        (AffineComplexPoints.algebraPointSpace B)) where
  toFun φ := ⟨φ.comp includeLeft, φ.comp includeRight⟩
  invFun p := lift p.1 p.2 (fun _ _ => Commute.all _ _)
  left_inv φ := by
    apply Algebra.TensorProduct.ext
    · simp
    · ext b
      change (lift (φ.comp (includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B))
        (φ.comp (includeRight : B →ₐ[ℂ] A ⊗[ℂ] B))
        (fun _ _ => Commute.all _ _)) (1 ⊗ₜ[ℂ] b) =
        φ (1 ⊗ₜ[ℂ] b)
      simp
      rw [← Algebra.TensorProduct.one_def, map_one, one_mul]
  right_inv p := by
    apply Prod.ext
    · simp
    · simp

/-- The algebra-valued complex points of an affine product have the actual
product evaluation topology. -/
def homeomorph :
    (AffineComplexPoints.algebraPointSpace (A ⊗[ℂ] B)) ≃ₜ
      ((AffineComplexPoints.algebraPointSpace A) ×
        (AffineComplexPoints.algebraPointSpace B)) where
  toEquiv := pointEquiv A B
  continuous_toFun := by
    apply Continuous.prodMk
    · apply (AffineComplexPoints.isEmbedding_evaluation A).isInducing.continuous_iff.mpr
      apply continuous_pi
      intro a
      change Continuous (fun φ : AffineComplexPoints.algebraPointSpace (A ⊗[ℂ] B) =>
        φ ((includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) a))
      exact AffineComplexPoints.continuous_evaluation (A ⊗[ℂ] B)
        ((includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) a)
    · apply (AffineComplexPoints.isEmbedding_evaluation B).isInducing.continuous_iff.mpr
      apply continuous_pi
      intro b
      change Continuous (fun φ : AffineComplexPoints.algebraPointSpace (A ⊗[ℂ] B) =>
        φ ((includeRight : B →ₐ[ℂ] A ⊗[ℂ] B) b))
      exact AffineComplexPoints.continuous_evaluation (A ⊗[ℂ] B)
        ((includeRight : B →ₐ[ℂ] A ⊗[ℂ] B) b)
  continuous_invFun := by
    apply (AffineComplexPoints.isEmbedding_evaluation (A ⊗[ℂ] B)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        change Continuous (fun p : AffineComplexPoints.algebraPointSpace A ×
          AffineComplexPoints.algebraPointSpace B => p.1 a * p.2 b)
        exact ((AffineComplexPoints.continuous_evaluation A a).comp continuous_fst).mul
          ((AffineComplexPoints.continuous_evaluation B b).comp continuous_snd)
    | add x y hx hy =>
        change Continuous (fun p : AffineComplexPoints.algebraPointSpace A ×
          AffineComplexPoints.algebraPointSpace B =>
            (pointEquiv A B).invFun p (x + y))
        have heq : (fun p : AffineComplexPoints.algebraPointSpace A ×
            AffineComplexPoints.algebraPointSpace B =>
              (pointEquiv A B).invFun p (x + y)) =
            (fun p => (pointEquiv A B).invFun p x + (pointEquiv A B).invFun p y) := by
          funext p
          exact map_add ((pointEquiv A B).invFun p) x y
        rw [heq]
        exact hx.add hy

end HodgeConjecture.AffineComplexPointsProduct

end
