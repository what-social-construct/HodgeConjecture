import HodgeConjecture.Collision.Algebra
import HodgeConjecture.Collision.ClopenDecomposition
import HodgeConjecture.Collision.ComponentSelectors
import HodgeConjecture.Collision.CollisionDiagonal
import HodgeConjecture.Collision.EtaleDecomposition
import HodgeConjecture.Collision.GlobalGeometry
import HodgeConjecture.Collision.PolynomialFiberProduct
import HodgeConjecture.Collision.SchemeDecomposition

/-!
# Collision stage

This umbrella module collects the complete collision stage:

* polynomial and tensor-product collision algebras;
* the global self-fiber product `R_f = X ×[Y] X`;
* the relative diagonal and its obstruction ideal sheaf;
* intrinsic annihilator and ambient sheaf-colon residuals;
* diagonal/off-diagonal component-selector conventions;
* affine compatibility with `A ⊗[B] A`;
* the canonical affine-scheme coproduct decomposition, with its first
  component identified with the actual relative diagonal;
* the global clopen collision decomposition for separated étale—and hence
  finite étale—morphisms;
* a reusable global witness for a literal decomposition
  `X ×[Y] X ≅ X ⨿ Rᵒᶠᶠ`, together with the component maps into `X ×[S] X`.

The idempotents in this stage use multiplication in a coordinate ring and
classify clopen scheme components.  Turning their components into Chow
correspondences, and proving idempotence for correspondence composition, are
separate realization inputs.
-/
