import HodgeConjecture.CommutativeAlgebra.FiniteTensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.Etale

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
    (hA : IsEtale (Spec.map (CommRingCat.ofHom (algebraMap B A)))) :
    IsEtale (Spec.map (CommRingCat.ofHom
      (algebraMap B (⨂[B] _ : ι, A)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @IsEtale)).mpr
  apply piTensorProduct_ringHomProperty
    (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 0))
    (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
    (RingHom.locally_holdsForLocalizationAway
      RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities
    (RingHom.locally_stableUnderComposition
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves 0)
      (fun _ _ _ _ _ _ _ _ hf hg =>
        RingHom.IsStandardSmoothOfRelativeDimension.comp hg hf))
    (RingHom.locally_isStableUnderBaseChange
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange 0)) ι
  exact (HasRingHomProperty.Spec_iff (P := @IsEtale)).mp hA

end HodgeConjecture.CollisionFoundations
