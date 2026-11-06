module

public import HodgeConjecture.CommutativeAlgebra.FiniteTensorProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

/-!
# Scheme-étale finite tensor sources

An actual étale affine structure map gives an étale structure map on the
existing finite tensor product. This uses its locally standard-smooth
presentations and their stability properties, not a converse from algebraic
étaleness to the scheme-theoretic definition.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry
open scoped TensorProduct

universe u

variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]

/-- A finite tensor product of an actual affine étale scheme is étale over
the same affine base, on its original algebra and structural map. -/
theorem piTensorProduct_isEtale (ι : Type u) [Finite ι]
    (hA : Etale (Spec.map (CommRingCat.ofHom (algebraMap B A)))) :
    Etale (Spec.map (CommRingCat.ofHom
      (algebraMap B (⨂[B] _ : ι, A)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  apply piTensorProduct_ringHomProperty RingHom.Etale
    RingHom.Etale.respectsIso RingHom.Etale.containsIdentities
    RingHom.Etale.stableUnderComposition RingHom.Etale.isStableUnderBaseChange ι
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hA

end HodgeConjecture.CollisionFoundations
