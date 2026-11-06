module

public import HodgeConjecture.Collision.IdealSheaf
public import HodgeConjecture.Collision.SheafColon
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

/-!
# Global collision geometry

For a scheme morphism `f : X ⟶ Y`, this file packages the global objects

* `R_f = X ×[Y] X`;
* the relative diagonal `X ⟶ R_f`;
* its obstruction ideal sheaf inside `R_f`;
* the canonical map `R_f ⟶ X × X`;
* the ambient residual ideal sheaf `I_{R_f} : I_Δ`.

The intrinsic residual on `R_f` is the annihilator of the relative diagonal
ideal.  The ambient residual is defined with the sheaf-colon construction, so
it is the largest quasi-coherent ideal-sheaf datum contained affine-locally in
the ordinary colon ideals.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section CollisionSpace

variable {X Y : Scheme.{u}}

/-- The global self-collision space `R_f = X ×[Y] X`. -/
abbrev collisionSpace (f : X ⟶ Y) : Scheme.{u} :=
  pullback f f

/-- The first projection from the self-collision space. -/
abbrev collisionFst (f : X ⟶ Y) :
    collisionSpace f ⟶ X :=
  pullback.fst f f

/-- The second projection from the self-collision space. -/
abbrev collisionSnd (f : X ⟶ Y) :
    collisionSpace f ⟶ X :=
  pullback.snd f f

/-- The relative diagonal `X ⟶ X ×[Y] X`. -/
abbrev collisionDiagonal (f : X ⟶ Y) :
    X ⟶ collisionSpace f :=
  pullback.diagonal f

/-- The canonical map from the relative self-collision space to `X × X`. -/
def collisionToProduct (f : X ⟶ Y) :
    collisionSpace f ⟶ X ⨯ X :=
  prod.lift (collisionFst f) (collisionSnd f)

/-- The absolute diagonal of `X`. -/
def absoluteDiagonal (X : Scheme.{u}) :
    X ⟶ X ⨯ X :=
  prod.lift (𝟙 X) (𝟙 X)

/--
The relative diagonal followed by `R_f ⟶ X × X` is the absolute diagonal.
-/
@[reassoc (attr := simp)]
theorem collisionDiagonal_comp_collisionToProduct
    (f : X ⟶ Y) :
    collisionDiagonal f ≫ collisionToProduct f =
      absoluteDiagonal X := by
  ext <;> simp [collisionToProduct, absoluteDiagonal]

end CollisionSpace

section AmbientOverBase

variable {S X Y : Scheme.{u}}

/--
For a factorization `X ⟶ Y ⟶ S`, the relative self-collision over `Y` maps
canonically to the ambient product `X ×[S] X`.
-/
def collisionToAmbientProduct
    (f : X ⟶ Y) (g : Y ⟶ S) :
    collisionSpace f ⟶ pullback (f ≫ g) (f ≫ g) :=
  pullback.mapDesc f f g

/--
If `Y` is separated over `S`, then `R_f ⟶ X ×[S] X` is a closed immersion,
so its kernel ideal sheaf is genuinely the ideal of the collision space in
the ambient product.
-/
instance collisionToAmbientProduct_isClosedImmersion
    (f : X ⟶ Y) (g : Y ⟶ S) [IsSeparated g] :
    IsClosedImmersion (collisionToAmbientProduct f g) := by
  change IsClosedImmersion (pullback.mapDesc f f g)
  infer_instance

/--
The relative diagonal over `Y`, followed by the ambient map, is the relative
diagonal of `X` over `S`.
-/
@[reassoc (attr := simp)]
theorem collisionDiagonal_comp_collisionToAmbientProduct
    (f : X ⟶ Y) (g : Y ⟶ S) :
    collisionDiagonal f ≫ collisionToAmbientProduct f g =
      pullback.diagonal (f ≫ g) := by
  ext <;> simp [collisionToAmbientProduct]

end AmbientOverBase

section IdealSheaves

variable {X Y : Scheme.{u}}

/--
The collision obstruction ideal `I_{Δ/R_f}` on the self-collision space.

It measures the scheme-theoretic difference between the relative diagonal
and the whole collision space.  It is not the cokernel obstruction to
algebraic realization of a Hodge projector.
-/
abbrev collisionObstructionIdealSheaf
    (f : X ⟶ Y) :
    (collisionSpace f).IdealSheafData :=
  relativeDiagonalIdealSheaf f

/--
The kernel ideal-sheaf datum of `R_f ⟶ X × X`.  When this map is a closed
immersion, this is the actual ideal sheaf of `R_f` in the ambient product.
-/
def ambientCollisionIdealSheaf
    (f : X ⟶ Y) :
    (X ⨯ X).IdealSheafData :=
  (collisionToProduct f).ker

/-- The ideal sheaf of the absolute diagonal in `X × X`. -/
def ambientDiagonalIdealSheaf
    (X : Scheme.{u}) :
    (X ⨯ X).IdealSheafData :=
  (absoluteDiagonal X).ker

/--
Because the relative diagonal factors through `R_f`, the ambient collision
ideal is contained in the ambient diagonal ideal.
-/
theorem ambientCollisionIdealSheaf_le_ambientDiagonalIdealSheaf
    (f : X ⟶ Y) :
    ambientCollisionIdealSheaf f ≤
      ambientDiagonalIdealSheaf X := by
  change
    (collisionToProduct f).ker ≤
      (absoluteDiagonal X).ker
  rw [← collisionDiagonal_comp_collisionToProduct f]
  exact Scheme.Hom.le_ker_comp (collisionDiagonal f) (collisionToProduct f)

/--
The intrinsic residual off-diagonal ideal on `R_f`, defined as the
annihilator of `I_{Δ/R_f}`.
-/
def intrinsicOffDiagonalIdealSheaf
    (f : X ⟶ Y) :
    (collisionSpace f).IdealSheafData :=
  CollisionIdealSheaf.annihilator
    (collisionObstructionIdealSheaf f)

/-- The intrinsic residual off-diagonal closed subscheme of `R_f`. -/
def intrinsicOffDiagonalScheme
    (f : X ⟶ Y) :
    Scheme.{u} :=
  (intrinsicOffDiagonalIdealSheaf f).subscheme

/--
The ambient sheaf-colon residual

`I_off = I_{R_f} : I_Δ`

inside `X × X`.
-/
def ambientOffDiagonalIdealSheaf
    (f : X ⟶ Y) :
    (X ⨯ X).IdealSheafData :=
  CollisionIdealSheaf.colon
    (ambientCollisionIdealSheaf f)
    (ambientDiagonalIdealSheaf X)

/--
On an affine ambient product, the global sections of the residual sheaf are
the literal ring-theoretic colon.
-/
theorem ambientOffDiagonalIdealSheaf_ideal_top
    [IsAffine (X ⨯ X)]
    (f : X ⟶ Y) :
    (ambientOffDiagonalIdealSheaf f).ideal
        ⟨⊤, isAffineOpen_top (X ⨯ X)⟩ =
      ((ambientCollisionIdealSheaf f).ideal
          ⟨⊤, isAffineOpen_top (X ⨯ X)⟩).colon
        ((ambientDiagonalIdealSheaf X).ideal
          ⟨⊤, isAffineOpen_top (X ⨯ X)⟩) :=
  CollisionIdealSheaf.colon_ideal_top _ _

/-- The ambient residual off-diagonal closed subscheme of `X × X`. -/
def ambientOffDiagonalScheme
    (f : X ⟶ Y) :
    Scheme.{u} :=
  (ambientOffDiagonalIdealSheaf f).subscheme

end IdealSheaves

section IdealSheavesOverBase

variable {S X Y : Scheme.{u}}

/--
The kernel ideal-sheaf datum of `R_f ⟶ X ×[S] X`.  If `Y ⟶ S` is separated,
the map is a closed immersion by
`collisionToAmbientProduct_isClosedImmersion`, so this is its defining ideal
sheaf.
-/
def ambientCollisionIdealSheafOver
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (pullback (f ≫ g) (f ≫ g)).IdealSheafData :=
  (collisionToAmbientProduct f g).ker

/-- The ideal sheaf of the diagonal of `X` inside `X ×[S] X`. -/
def ambientDiagonalIdealSheafOver
    (p : X ⟶ S) :
    (pullback p p).IdealSheafData :=
  (pullback.diagonal p).ker

/--
The collision space lies inside the ambient diagonal incidence condition:
`I_{R_f} ≤ I_Δ`.
-/
theorem ambientCollisionIdealSheafOver_le_ambientDiagonalIdealSheafOver
    (f : X ⟶ Y) (g : Y ⟶ S) :
    ambientCollisionIdealSheafOver f g ≤
      ambientDiagonalIdealSheafOver (f ≫ g) := by
  change
    (collisionToAmbientProduct f g).ker ≤
      (pullback.diagonal (f ≫ g)).ker
  rw [← collisionDiagonal_comp_collisionToAmbientProduct f g]
  exact
    Scheme.Hom.le_ker_comp
      (collisionDiagonal f)
      (collisionToAmbientProduct f g)

/--
The ambient residual in the geometrically relevant product over `S`:

`I_off = I_{R_f} : I_Δ`.
-/
def ambientOffDiagonalIdealSheafOver
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (pullback (f ≫ g) (f ≫ g)).IdealSheafData :=
  CollisionIdealSheaf.colon
    (ambientCollisionIdealSheafOver f g)
    (ambientDiagonalIdealSheafOver (f ≫ g))

/--
On an affine ambient product over `S`, the residual global ideal is exactly
the corresponding ring colon.
-/
theorem ambientOffDiagonalIdealSheafOver_ideal_top
    (f : X ⟶ Y) (g : Y ⟶ S)
    [IsAffine (pullback (f ≫ g) (f ≫ g))] :
    (ambientOffDiagonalIdealSheafOver f g).ideal
        ⟨⊤, isAffineOpen_top
          (pullback (f ≫ g) (f ≫ g))⟩ =
      ((ambientCollisionIdealSheafOver f g).ideal
          ⟨⊤, isAffineOpen_top
            (pullback (f ≫ g) (f ≫ g))⟩).colon
        ((ambientDiagonalIdealSheafOver (f ≫ g)).ideal
          ⟨⊤, isAffineOpen_top
            (pullback (f ≫ g) (f ≫ g))⟩) :=
  CollisionIdealSheaf.colon_ideal_top _ _

/-- The ambient residual closed subscheme inside `X ×[S] X`. -/
def ambientOffDiagonalSchemeOver
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Scheme.{u} :=
  (ambientOffDiagonalIdealSheafOver f g).subscheme

end IdealSheavesOverBase

end

end HodgeConjecture
