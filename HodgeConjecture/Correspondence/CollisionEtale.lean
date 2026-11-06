module

public import HodgeConjecture.Collision.EtaleDecomposition
public import HodgeConjecture.Correspondence.Collision
public import HodgeConjecture.Correspondence.Etale

@[expose] public section

/-!
# Finite étale collision correspondences

This module is the bridge between the global étale collision decomposition
and the reusable finite-étale correspondence layer.

For a finite étale morphism `f`, both projections

`X ×[Y] X ⇉ X`

are finite étale by base change.  The off-diagonal component in any clopen
collision decomposition also has finite étale legs.  In particular, the
canonical decomposition constructed in `Collision.EtaleDecomposition` stays
inside the finite-étale admissible correspondence class.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S X Y : Scheme.{u}}

/--
If `f` is finite étale, both projections of its self-collision
correspondence are finite étale: each is a base change of `f`.
-/
theorem collisionSchemeCorrespondence_hasFiniteEtaleLegs
    (f : X ⟶ Y) (g : Y ⟶ S)
    [IsFinite f] [Etale f] :
    SchemeCorrespondence.HasFiniteEtaleLegs
      (collisionSchemeCorrespondence f g) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · change Etale (pullback.fst f f)
      exact
        MorphismProperty.pullback_fst
          f f (inferInstance : Etale f)
    · change Etale (pullback.snd f f)
      exact
        MorphismProperty.pullback_snd
          f f (inferInstance : Etale f)
  · change IsFinite (pullback.fst f f)
    exact
      MorphismProperty.pullback_fst
        f f (inferInstance : IsFinite f)
  · change IsFinite (pullback.snd f f)
    exact
      MorphismProperty.pullback_snd
        f f (inferInstance : IsFinite f)

namespace CollisionSchemeDecomposition

variable {f : X ⟶ Y}

/--
For finite étale `f`, the off-diagonal component of any collision
decomposition has finite étale legs.
-/
theorem offDiagonalSchemeCorrespondence_hasFiniteEtaleLegs
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S)
    [IsFinite f] [Etale f] :
    SchemeCorrespondence.HasFiniteEtaleLegs
      (D.offDiagonalSchemeCorrespondence g) := by
  letI : Etale (collisionFst f) :=
    MorphismProperty.pullback_fst
      f f (inferInstance : Etale f)
  letI : Etale (collisionSnd f) :=
    MorphismProperty.pullback_snd
      f f (inferInstance : Etale f)
  letI : IsFinite (collisionFst f) :=
    MorphismProperty.pullback_fst
      f f (inferInstance : IsFinite f)
  letI : IsFinite (collisionSnd f) :=
    MorphismProperty.pullback_snd
      f f (inferInstance : IsFinite f)
  letI : Etale D.offDiagonalInclusion := by
    infer_instance
  letI : IsFinite D.offDiagonalInclusion := by
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · change Etale
        (D.offDiagonalInclusion ≫ collisionFst f)
      infer_instance
    · change Etale
        (D.offDiagonalInclusion ≫ collisionSnd f)
      infer_instance
  · change IsFinite
      (D.offDiagonalInclusion ≫ collisionFst f)
    infer_instance
  · change IsFinite
      (D.offDiagonalInclusion ≫ collisionSnd f)
    infer_instance

end CollisionSchemeDecomposition

end

end HodgeConjecture
