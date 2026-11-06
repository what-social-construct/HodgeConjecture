module

public import HodgeConjecture.Collision.ClopenDecomposition
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

/-!
# Global collision decomposition for separated étale morphisms

If `f : X ⟶ Y` is étale, its relative diagonal

`X ⟶ X ×[Y] X`

is an open immersion.  If `f` is also separated, the same diagonal is a
closed immersion.  Its open complement therefore exists as a scheme and the
self-collision space is globally the disjoint union of the diagonal and that
complement.

Finite étale morphisms are the main application: finiteness supplies
separatedness automatically.  Étaleness alone is not enough, since an étale
morphism need not be separated.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- The open complement of the diagonal in the collision space. -/
noncomputable def collisionOffDiagonalOpen
    (f : X ⟶ Y) [IsSeparated f] [Etale f] :
    (collisionSpace f).Opens :=
  ⟨((collisionDiagonal f).opensRange :
      Set (collisionSpace f))ᶜ,
    (collisionDiagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/--
The diagonal and its open complement form a coproduct presentation of the
collision space.
-/
noncomputable def collisionDecompositionCofanIsColimit
    (f : X ⟶ Y) [IsSeparated f] [Etale f] :
    IsColimit
      (BinaryCofan.mk
        (collisionDiagonal f)
        (collisionOffDiagonalOpen f).ι) :=
  Nonempty.some
    (nonempty_isColimit_binaryCofanMk_of_isCompl
      (collisionDiagonal f)
      (collisionOffDiagonalOpen f).ι
      (by
        rw [Scheme.Opens.opensRange_ι]
        apply IsCompl.of_eq
        · ext x
          simp [collisionOffDiagonalOpen]
        · ext x
          simp [collisionOffDiagonalOpen]))

/--
The global diagonal/off-diagonal collision decomposition of a separated
étale morphism.
-/
noncomputable def separatedEtaleCollisionSchemeDecomposition
    (f : X ⟶ Y) [IsSeparated f] [Etale f] :
    CollisionSchemeDecomposition f where
  offDiagonal := collisionOffDiagonalOpen f
  decomposition :=
    IsColimit.coconePointUniqueUpToIso
      (collisionDecompositionCofanIsColimit f)
      (colimit.isColimit
        (pair X (collisionOffDiagonalOpen f)))
  diagonal_hom := by
    simpa using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (collisionDecompositionCofanIsColimit f)
        (colimit.isColimit
          (pair X (collisionOffDiagonalOpen f)))
        ⟨WalkingPair.left⟩

/--
Finite étale morphisms canonically enter the separated-étale collision
decomposition.
-/
noncomputable def finiteEtaleCollisionSchemeDecomposition
    (f : X ⟶ Y) [IsFinite f] [Etale f] :
    CollisionSchemeDecomposition f :=
  separatedEtaleCollisionSchemeDecomposition f

end

end HodgeConjecture
