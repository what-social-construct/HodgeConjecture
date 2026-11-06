module

public import HodgeConjecture.Boundary.Normalization.GenericFiber

@[expose] public section

/-!
# Base change of the actual generic fiber

The spectrum of `E ⊗[K(X)] K(Y)` is the actual base change of a finite
dominant morphism along `Spec E → Spec K(X) → X`. The tensor order retains
the extension algebra in the first factor. Both projections are the original
tensor inclusions and generic-stalk map; no replacement fiber is introduced.
The result applies to any commutative `K(X)`-algebra, without separability.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles
open scoped TensorProduct

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

/-- The actual tensor spectrum realizes base change of the generic-stalk
square along any commutative algebra over the original base function field.
Its canonical pullback isomorphism preserves both displayed projections. -/
theorem functionFieldMapOfDominant_baseChange_isPullback
    (E : Type u) [CommRing E] [Algebra X.functionField E] :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Y.functionField →ₐ[X.functionField]
          E ⊗[X.functionField] Y.functionField).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          E →+* E ⊗[X.functionField] Y.functionField)))
      p
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField E)) ≫
        X.fromSpecStalk (genericPoint X)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct X.functionField E Y.functionField)).flip.paste_horiz
      (functionFieldMapOfDominant_isPullback p)

end

end HodgeConjecture.CollisionFoundations
